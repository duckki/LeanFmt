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

private def rebaseLines (sourceColumn targetColumn : Nat) : List String → List String
  | [] => []
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

private def rebaseTreeText
    (source : String) (tree : SyntaxTree.Tree)
    (sourceColumn targetColumn : Nat)
    : String :=
  let rec loop (previous : SyntaxTree.Token) (parts : List String)
      : List SyntaxTree.Token → List String
    | [] => parts
    | token :: rest =>
        let trivia := SyntaxTree.sourceText source previous.span.stop token.span.start
        let trivia := rebaseTextIndent sourceColumn targetColumn trivia
        loop token (token.lexeme :: trivia :: parts) rest
  match tree.tokens.toList with
  | [] => ""
  | first :: rest => String.join <| (loop first [first.lexeme] rest).reverse

private def fittingTargetColumn
    (source : String) (tree : SyntaxTree.Tree) (sourceText : String)
    (sourceColumn targetColumn lineWidthLimit suffixWidth : Nat)
    : Nat :=
  if targetColumn <= sourceColumn then
    targetColumn
  else
    let rebasedText := rebaseTreeText source tree sourceColumn targetColumn
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

private def continuationIndent? (text : String) : Option Nat :=
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

private def currentLineAfterAppend (currentLine text : String) : String :=
  if text.contains '\n' || text.contains '\r' then
    charsAfterLastNewline text
  else
    currentLine ++ text

private def isProofTree (tree : SyntaxTree.Tree) : Bool :=
  match tree with
  | .node .proofBody _ => true
  | _ => false

private def isQuotationTree : SyntaxTree.Tree → Bool
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

private partial def containsQuotationTree : SyntaxTree.Tree → Bool
  | .missing => false
  | .leaf _ => false
  | tree@(.node _ children) =>
      isQuotationTree tree || children.any containsQuotationTree

private partial def containsQuotationOutsideProofTree : SyntaxTree.Tree → Bool
  | .missing => false
  | .leaf _ => false
  | tree@(.node _ children) =>
      if isProofTree tree then
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

private def sourceBreakBeforeLexeme (tree : SyntaxTree.Tree) (lexeme : String) : Bool :=
  let rec loop (started sawBreak : Bool) : List SyntaxTree.Token → Bool
    | [] => false
    | token :: rest =>
        if token.lexeme == lexeme then
          sawBreak
        else
          loop true
            (sawBreak || (started && SpaceRules.hasLineStructure token.leading.text))
            rest
  loop false false tree.tokens.toList

private def isLayoutSensitiveCommand : SyntaxTree.Tree → Bool
  | .node (.raw `Lean.Parser.Command.syntax) _ => true
  | .node (.raw `Lean.Parser.Command.syntaxAbbrev) _ => true
  | tree@(.node (.raw `Lean.Parser.Command.macro) _) =>
      sourceBreakBeforeLexeme tree "=>"
  | .node (.raw `Lean.Parser.Command.macro_rules) _ => true
  | .node (.raw `Lean.Parser.Command.elab) _ => true
  | .node (.raw `Lean.Parser.Command.elab_rules) _ => true
  | .node (.raw `Lean.Parser.«command_Simproc_decl_(_):=_») _ => true
  | .node (.raw `Lean.Parser.«command__Simproc__[_]_(_):=_») _ => true
  | .node (.raw `Lean.runCmd) _ => true
  | .node (.raw `Batteries.Tactic.Alias.alias) _ => true
  | .node (.raw `Batteries.Tactic.Alias.aliasLR) _ => true
  | _ => false

private def isMathlibTacticSyntaxTree : SyntaxTree.Tree → Bool
  | .node kind _ =>
      (SyntaxTree.nodeKindName kind).startsWith "Mathlib.Tactic."
  | _ => false

private def isCalcTree : SyntaxTree.Tree → Bool
  | .node (.raw `Lean.calc) _ => true
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
  | .node (.raw `Lean.Parser.Command.moduleDoc) _ => true
  | .node (.raw `Lean.Parser.Command.docComment) _ => true
  | _ => false

private partial def containsProofTree : SyntaxTree.Tree → Bool
  | .missing => false
  | .leaf _ => false
  | tree@(.node _ children) =>
      isProofTree tree || children.any containsProofTree

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
      match children[1]? with
      | some argument =>
          LineBreakRules.treeFirstLexeme? argument == some "fun"
          && containsProofTree argument
      | none => false
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

private def isProofLemmaCommand (tree : SyntaxTree.Tree) : Bool :=
  match tree with
  | .node (.raw `lemma) _ =>
      LineBreakRules.treeFirstLexeme? tree == some "lemma" && containsProofTree tree
  | .node (.raw `group) _ =>
      LineBreakRules.treeFirstLexeme? tree == some "lemma" && containsProofTree tree
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
  else if isProofTree tree then
    some .proof
  else if isProofLayoutIsland tree then
    some .proofLayout
  else if isProofLemmaCommand tree then
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
  else if isMathlibTacticSyntaxTree tree then
    some .mathlibTactic
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
  | .proofWidgetsJsx => true
  | _ => false

def LayoutIslandKind.isProof : LayoutIslandKind → Bool
  | .proof => true
  | _ => false

def LayoutIslandKind.isProofWidgetsJsx : LayoutIslandKind → Bool
  | .proofWidgetsJsx => true
  | _ => false

def LayoutIslandKind.isQuotation : LayoutIslandKind → Bool
  | .quotation => true
  | _ => false

def LayoutIslandKind.usesPendingIndent : LayoutIslandKind → Bool
  | .proof | .proofLemma | .proofWidgetsJsx | .quotation | .syntaxComment => true
  | _ => false

def LayoutIslandKind.preservesFollowingCommentIndent : LayoutIslandKind → Bool
  | .layoutSensitiveCommand => true
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
  let proofWidgetsJsx := classification?.any LayoutIslandKind.isProofWidgetsJsx
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
    if usesPendingIndent then
      request.pendingLeadingWhitespace?.getD originalLeading
    else
      originalLeading
  let leadingColumn := lineWidth <| currentLineAfterAppend request.currentLine leading
  let sourceText :=
    SyntaxTree.sourceText request.source firstToken.span.start lastToken.span.stop
  let sourceColumn := request.sourceMap.columnAt firstToken.span.start
  let retainsRelativeLayout := proof || proofWidgetsJsx || quotation
  let hasLineBreakTrivia := retainsRelativeLayout && treeHasLineBreakTrivia tree
  let originalLeadingHasLineStructure := SpaceRules.hasLineStructure originalLeading
  let detachedInlineProofBody :=
    proof
    && hasLineBreakTrivia
    && usesPendingIndent
    && !originalLeadingHasLineStructure
    && SpaceRules.hasLineStructure leading
  let inlineMultilineLayoutIsland :=
    retainsRelativeLayout
    && hasLineBreakTrivia
    && !originalLeadingHasLineStructure
    && !detachedInlineProofBody
  let inlineContinuationColumns? :=
    if !inlineMultilineLayoutIsland then
      none
    else
      match continuationIndent? sourceText, request.lastToken? with
      | some sourceIndent, some leftToken =>
          let sourceAnchor := request.sourceMap.columnAt leftToken.span.start
          let outputAnchor := lineWidth request.currentLine - leftToken.lexeme.length
          let movedIndent := shiftColumnByAnchor sourceAnchor outputAnchor sourceIndent
          let structuralIndent :=
            if proof then
              (request.segmentIndentation + 1) * indentationSpaces
            else if usesPendingIndent then
              leadingColumn
            else
              request.currentIndent
          let movedIndent :=
            if sourceAnchor < sourceIndent then
              movedIndent
            else
              sourceIndent
          some (sourceIndent, max movedIndent structuralIndent)
      | _, _ => none
  let inlineContinuationColumns? :=
    match inlineContinuationColumns? with
    | some (sourceIndent, targetIndent) =>
        if quotation then
          some
            (
              sourceIndent,
              fittingTargetColumn request.source tree sourceText
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
  let targetColumn? :=
    if proof && originalLeadingHasLineStructure then
      targetColumn?.map
        fun targetColumn =>
          max request.outputLayoutBaseColumn targetColumn
    else
      targetColumn?
  let targetColumn? :=
    if (proof || quotation) && !inlineMultilineLayoutIsland then
      targetColumn?.map
        fun targetColumn =>
          fittingTargetColumn request.source tree sourceText sourceColumn
            targetColumn request.lineWidth request.lineFitSuffixWidth
    else
      targetColumn?
  let leading :=
    match targetColumn? with
    | some targetColumn =>
        rebaseTextIndent
          (if usesPendingIndent then leadingColumn else sourceColumn)
          targetColumn leading
    | none => leading
  let sourceTextRebase? :=
    match inlineContinuationColumns?,
          request.rebaseSourceTextTargetColumn? with
    | some continuationColumns, some targetColumn =>
        if proof then
          some (sourceColumn, targetColumn)
        else
          some continuationColumns
    | some continuationColumns, none => some continuationColumns
    | none, some targetColumn => some (sourceColumn, targetColumn)
    | none, none =>
        targetColumn?.map
          fun targetColumn =>
            (sourceColumn, targetColumn)
  let sourceText :=
    match sourceTextRebase? with
    | some (sourceIndent, targetIndent) =>
        if sourceIndent == targetIndent then
          sourceText
        else
          rebaseTreeText request.source tree sourceIndent targetIndent
    | none => sourceText
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
