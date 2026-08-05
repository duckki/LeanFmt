import LeanFmt.LeanEnvironment

namespace LeanFmt
namespace SyntaxTree

open Lean

/-! ## Lossless source model -/

structure Span where
  start : String.Pos.Raw
  stop : String.Pos.Raw
deriving BEq, Repr

namespace Span

def fromSubstring (substring : Substring.Raw) : Span :=
  { start := substring.startPos, stop := substring.stopPos }

end Span

structure Trivia where
  span : Span
  text : String
deriving BEq, Repr

namespace Trivia

def fromSubstring (substring : Substring.Raw) : Trivia :=
  { span := Span.fromSubstring substring, text := substring.toString }

end Trivia

inductive TokenRole where
  | atom
  | ident
deriving BEq, Repr

structure Token where
  role : TokenRole
  kind : SyntaxNodeKind
  value : String
  lexeme : String
  leading : Trivia
  trailing : Trivia
  span : Span
deriving BEq, Repr

namespace Token

def fullSpan (token : Token) : Span :=
  { start := token.leading.span.start, stop := token.trailing.span.stop }

def fullText (token : Token) : String :=
  token.leading.text ++ token.lexeme ++ token.trailing.text

end Token

inductive NodeKind where
  | raw (kind : SyntaxNodeKind)
  | tactic (kind : SyntaxNodeKind) (containsSequence isOwner containsOwner : Bool)
  | letExpression (kind : SyntaxNodeKind) (bodyCanStartApplicationArgument : Bool)
  | application
  | infixChain (kind : SyntaxNodeKind)
  | lowPriorityInfixRhs
  | indexedInfix (kind : SyntaxNodeKind)
  | suffixGroup
  | tacticEliminationTargets (containsNamed : Bool)
  | tacticEliminationHeader (targetIsNamed : Bool)
  | namedDiscriminant
  | patternLambda
  | definition
  | annotatedDeclaration
  | signatureParameters
  | structureHeader
  | structureConstructor
  | structureDeriving
  | matchDiscriminants
  | matchPatterns
  | doForHeader
  | doFallbackClause
  | doFallbackContinuation
  | structureUpdate
  | ifThenElseClause
  | ifThenElseChain
  | proofBody (containsTacticLayoutOwner : Bool)
  | derivingClause
  | unifConstraints
deriving BEq, Inhabited, Repr

def nodeKindName : NodeKind → String
  | .raw kind => toString kind
  | .tactic kind _ _ _ => toString kind
  | .letExpression kind bodyCanStartApplicationArgument =>
      s!"LeanFmt.SyntaxTree.NodeKind.letExpression {kind} {bodyCanStartApplicationArgument}"
  | .application => "LeanFmt.SyntaxTree.NodeKind.application"
  | .infixChain kind => s!"LeanFmt.SyntaxTree.NodeKind.infixChain {kind}"
  | .lowPriorityInfixRhs => "LeanFmt.SyntaxTree.NodeKind.lowPriorityInfixRhs"
  | .indexedInfix kind => s!"LeanFmt.SyntaxTree.NodeKind.indexedInfix {kind}"
  | .suffixGroup => "LeanFmt.SyntaxTree.NodeKind.suffixGroup"
  | .tacticEliminationTargets containsNamed =>
      s!"LeanFmt.SyntaxTree.NodeKind.tacticEliminationTargets {containsNamed}"
  | .tacticEliminationHeader targetIsNamed =>
      s!"LeanFmt.SyntaxTree.NodeKind.tacticEliminationHeader {targetIsNamed}"
  | .namedDiscriminant => "LeanFmt.SyntaxTree.NodeKind.namedDiscriminant"
  | .patternLambda => "LeanFmt.SyntaxTree.NodeKind.patternLambda"
  | .definition => "LeanFmt.SyntaxTree.NodeKind.definition"
  | .annotatedDeclaration => "LeanFmt.SyntaxTree.NodeKind.annotatedDeclaration"
  | .signatureParameters => "LeanFmt.SyntaxTree.NodeKind.signatureParameters"
  | .structureHeader => "LeanFmt.SyntaxTree.NodeKind.structureHeader"
  | .structureConstructor => "LeanFmt.SyntaxTree.NodeKind.structureConstructor"
  | .structureDeriving => "LeanFmt.SyntaxTree.NodeKind.structureDeriving"
  | .matchDiscriminants => "LeanFmt.SyntaxTree.NodeKind.matchDiscriminants"
  | .matchPatterns => "LeanFmt.SyntaxTree.NodeKind.matchPatterns"
  | .doForHeader => "LeanFmt.SyntaxTree.NodeKind.doForHeader"
  | .doFallbackClause => "LeanFmt.SyntaxTree.NodeKind.doFallbackClause"
  | .doFallbackContinuation => "LeanFmt.SyntaxTree.NodeKind.doFallbackContinuation"
  | .structureUpdate => "LeanFmt.SyntaxTree.NodeKind.structureUpdate"
  | .ifThenElseClause => "LeanFmt.SyntaxTree.NodeKind.ifThenElseClause"
  | .ifThenElseChain => "LeanFmt.SyntaxTree.NodeKind.ifThenElseChain"
  | .proofBody _ => "LeanFmt.SyntaxTree.NodeKind.proofBody"
  | .derivingClause => "LeanFmt.SyntaxTree.NodeKind.derivingClause"
  | .unifConstraints => "LeanFmt.SyntaxTree.NodeKind.unifConstraints"

inductive Tree where
  | missing
  | leaf (token : Token)
  | node (kind : NodeKind) (children : Array Tree)
deriving BEq, Inhabited, Repr

def isSyntaxCommentKind (kind : SyntaxNodeKind) : Bool :=
  kind == `Lean.Parser.Command.moduleDoc || kind == `Lean.Parser.Command.docComment

def isCoreTacticKindName (kindName : String) : Bool :=
  kindName.startsWith "Lean.Parser.Tactic."
  || kindName.startsWith "Lean.Elab.Tactic."
  || kindName.startsWith "tactic"
  || kindName.startsWith "«tactic"
  || kindName == "Lean.cdot"
  || kindName == "Lean.cdotTk"

def isExtensionTacticKindName (kindName : String) : Bool :=
  kindName.contains ".Tactic." && !isCoreTacticKindName kindName

namespace Tree

private partial def appendTokens (tokens : Array Token) : Tree → Array Token
  | Tree.missing => tokens
  | Tree.leaf token => tokens.push token
  | Tree.node _ children => children.foldl appendTokens tokens

def tokens (tree : Tree) : Array Token :=
  appendTokens #[] tree

def isTacticSequenceKind (kind : Lean.SyntaxNodeKind) : Bool :=
  kind == `Lean.Parser.Tactic.tacticSeq || kind == `Lean.Parser.Tactic.tacticSeq1Indented

def tacticKindOwnsStructuralLayout (kind : Lean.SyntaxNodeKind) : Bool :=
  kind == `Lean.Parser.Tactic.cases
  || kind == `Lean.Parser.Tactic.inductionAlts
  || kind == `Lean.Parser.Tactic.inductionAlt

def isCalcTree : Tree → Bool
  | .node (.raw `Lean.calc) _ => true
  | .node (.raw `Lean.calcTactic) _ => true
  | .node (.tactic `Lean.calcTactic _ _ _) _ => true
  | _ => false

def isTacticSequenceTree : Tree → Bool
  | .node (.raw kind) _ => isTacticSequenceKind kind
  | .node (.tactic kind _ _ _) _ => isTacticSequenceKind kind
  | _ => false

private partial def firstTacticToken? : Tree → Option Token
  | .missing => none
  | .leaf token => if token.lexeme.isEmpty then none else some token
  | .node _ children => children.findSome? firstTacticToken?

structure TacticLayoutSummary where
  containsSequence : Bool := false
  isOwner : Bool := false
  containsOwner : Bool := false
deriving Inhabited

partial def tacticLayoutSummary : Tree → TacticLayoutSummary
  | .missing | .leaf _ => {}
  | .node (.proofBody containsOwner) _ => { containsOwner }
  | .node (.tactic _ containsSequence isOwner containsOwner) _ =>
      { containsSequence, isOwner, containsOwner }
  | tree@(.node kind children) =>
      let childSummaries := children.map tacticLayoutSummary
      let containsSequence :=
        (match kind with
          | .proofBody _ => false
          | .raw rawKind =>
              isTacticSequenceKind rawKind || childSummaries.any (·.containsSequence)
          | _ => childSummaries.any (·.containsSequence))
      let isOwner :=
        isCalcTree tree
        || ((match kind with
              | .raw rawKind => tacticKindOwnsStructuralLayout rawKind
              | _ => false)
            && (children.zip childSummaries).any
                fun (child, summary) =>
                  !isTacticSequenceTree child && summary.containsSequence)
      let visibleOwner :=
        isOwner
        && (!isCalcTree tree
            || (firstTacticToken? tree).any fun token => token.leading.text.contains '\n')
      let hidesNestedOwners :=
        match kind with
        | .raw rawKind =>
            let kindName := nodeKindName kind
            (isCoreTacticKindName kindName || isExtensionTacticKindName kindName)
            && !isTacticSequenceKind rawKind
            && !isOwner
        | _ => false
      {
        containsSequence
        isOwner
        containsOwner :=
          !hidesNestedOwners && (visibleOwner || childSummaries.any (·.containsOwner))
      }

def isTacticLayoutOwner (tree : Tree) : Bool :=
  (tacticLayoutSummary tree).isOwner

def containsTacticLayoutOwner (tree : Tree) : Bool :=
  (tacticLayoutSummary tree).containsOwner

partial def protectNestedTacticSequences : Tree → Tree
  | tree@(.node (.tactic kind _ _ _) _) =>
      if isTacticSequenceKind kind then
        .node (.proofBody tree.containsTacticLayoutOwner) #[tree]
      else
        tree
  | .node kind children =>
      .node kind (children.map protectNestedTacticSequences)
  | tree => tree

def annotateTacticTree : Tree → Tree
  | tree@(.node (.raw kind) children) =>
      let kindName := nodeKindName (.raw kind)
      if isCoreTacticKindName kindName || isExtensionTacticKindName kindName then
        let summary := tacticLayoutSummary tree
        let children :=
          if summary.isOwner then
            children.map protectNestedTacticSequences
          else
            children
        .node
          (.tactic kind summary.containsSequence summary.isOwner summary.containsOwner)
          children
      else
        tree
  | tree => tree

private inductive TokenCardinality where
  | empty
  | single (token : Token)
  | multiple
deriving Inhabited

private def TokenCardinality.combine (left right : TokenCardinality) : TokenCardinality :=
  match left, right with
  | .multiple, _
  | _, .multiple
  | .single _, .single _ => .multiple
  | .single token, .empty
  | .empty, .single token => .single token
  | .empty, .empty => .empty

private partial def tokenCardinality : Tree → TokenCardinality
  | Tree.missing => .empty
  | Tree.leaf token => .single token
  | Tree.node _ children =>
      children.foldl
        (fun cardinality child =>
          match cardinality with
          | .multiple => .multiple
          | _ => cardinality.combine (tokenCardinality child))
        .empty

def singleToken? (tree : Tree) : Option Token :=
  match tokenCardinality tree with
  | .single token => some token
  | .empty
  | .multiple => none

partial def firstToken? : Tree → Option Token
  | Tree.missing => none
  | Tree.leaf token =>
      if token.lexeme.isEmpty then none else some token
  | Tree.node _ children =>
      children.foldl
        (fun found child =>
          match found with
          | some token => some token
          | none => firstToken? child)
        none

partial def lastToken? : Tree → Option Token
  | Tree.missing => none
  | Tree.leaf token =>
      if token.lexeme.isEmpty then none else some token
  | Tree.node _ children =>
      children.foldl
        (fun found child =>
          match lastToken? child with
          | some token => some token
          | none => found)
        none

partial def extractLeadingLexeme? (lexeme : String) : Tree → Option (Tree × Tree)
  | .leaf token =>
      if token.lexeme == lexeme then some (.leaf token, .missing) else none
  | .node kind children => do
      let index ← children.findIdx? fun child => child.firstToken?.isSome
      let child ← children[index]?
      let (leading, remainder) ← extractLeadingLexeme? lexeme child
      some (leading, .node kind (children.set! index remainder))
  | .missing => none

partial def extractTrailingLexeme? (lexeme : String) : Tree → Option (Tree × Tree)
  | .leaf token =>
      if token.lexeme == lexeme then some (.missing, .leaf token) else none
  | .node kind children => do
      let index ←
        (List.range children.size).foldl
          (fun found candidate =>
            if children[candidate]?.bind Tree.firstToken? |>.isSome then
              some candidate
            else
              found)
          none
      let child ← children[index]?
      let (remainder, trailing) ← extractTrailingLexeme? lexeme child
      some (.node kind (children.set! index remainder), trailing)
  | .missing => none

partial def containsNodeKind (target : NodeKind) : Tree → Bool
  | Tree.missing => false
  | Tree.leaf _ => false
  | Tree.node kind children =>
      kind == target || children.any (containsNodeKind target)

partial def firstNodeChildCount? (target : NodeKind) : Tree → Option Nat
  | Tree.missing => none
  | Tree.leaf _ => none
  | Tree.node kind children =>
      if kind == target then
        some children.size
      else
        children.foldl
          (fun found child =>
            match found with
            | some count => some count
            | none => firstNodeChildCount? target child)
          none

def firstInfixChainChildCount? (kind : SyntaxNodeKind) (tree : Tree) : Option Nat :=
  firstNodeChildCount? (.infixChain kind) tree

partial def syntaxCommentSpans : Tree → List Span
  | .missing | .leaf _ => []
  | tree@(.node (.raw kind) children) =>
      if isSyntaxCommentKind kind then
        match tree.firstToken?, tree.lastToken? with
        | some first, some last => [{ start := first.span.start, stop := last.span.stop }]
        | _, _ => []
      else
        children.toList.flatMap syntaxCommentSpans
  | .node _ children => children.toList.flatMap syntaxCommentSpans

end Tree

structure Module where
  source : String
  rawSyntax : Syntax
  tree : Tree
  tokens : Array Token
deriving Repr

namespace Module

def sourceOrderedTokens (moduleTree : Module) : Array Token :=
  moduleTree.tokens.qsort fun left right => left.fullSpan.start < right.fullSpan.start

def reconstruct (moduleTree : Module) : String :=
  let tokens := moduleTree.sourceOrderedTokens
  let body := tokens.foldl (fun acc token => acc ++ token.fullText) ""
  match tokens.back? with
  | none => moduleTree.source
  | some token =>
      body
      ++ String.Pos.Raw.extract
          moduleTree.source token.fullSpan.stop moduleTree.source.endPos.offset

end Module

def sourceText (source : String) (start stop : String.Pos.Raw) : String :=
  String.Pos.Raw.extract source start stop

structure SourcePositionMap where
  source : String
  lineStarts : Array String.Pos.Raw
deriving Repr

namespace SourcePositionMap

def ofString (source : String) : SourcePositionMap :=
  let fileMap := Lean.FileMap.ofString source
  { source, lineStarts := fileMap.positions }

def fileMap (sourceMap : SourcePositionMap) : Lean.FileMap :=
  { source := sourceMap.source, positions := sourceMap.lineStarts }

def columnAt (sourceMap : SourcePositionMap) (position : String.Pos.Raw) : Nat :=
  (sourceMap.fileMap.toPosition position).column

def lineNumberAt (sourceMap : SourcePositionMap) (position : String.Pos.Raw) : Nat :=
  (sourceMap.fileMap.toPosition position).line

end SourcePositionMap

def syntheticTrivia : Trivia :=
  { span := { start := 0, stop := 0 }, text := "" }

def tokenOfOriginal
    (source : String)
    (role : TokenRole)
    (kind : SyntaxNodeKind)
    (value : String)
    (leading : Substring.Raw)
    (startPos : String.Pos.Raw)
    (trailing : Substring.Raw)
    (stopPos : String.Pos.Raw)
    : Token :=
  {
    role
    kind
    value
    lexeme := sourceText source startPos stopPos
    leading := Trivia.fromSubstring leading
    trailing := Trivia.fromSubstring trailing
    span := { start := startPos, stop := stopPos }
  }

def tokenOfSynthetic
    (role : TokenRole)
    (kind : SyntaxNodeKind)
    (value : String)
    (startPos : String.Pos.Raw)
    (stopPos : String.Pos.Raw)
    : Token :=
  {
    role
    kind
    value
    lexeme := value
    leading := syntheticTrivia
    trailing := syntheticTrivia
    span := { start := startPos, stop := stopPos }
  }

def tokenOfNone (role : TokenRole) (kind : SyntaxNodeKind) (value : String) : Token :=
  {
    role
    kind
    value
    lexeme := value
    leading := syntheticTrivia
    trailing := syntheticTrivia
    span := { start := 0, stop := 0 }
  }

def tokenOfSourceInfo
    (source : String)
    (role : TokenRole)
    (kind : SyntaxNodeKind)
    (value : String)
    (info : SourceInfo)
    : Token :=
  match info with
  | .original leading startPos trailing stopPos =>
      tokenOfOriginal source role kind value leading startPos trailing stopPos
  | .synthetic startPos stopPos _ =>
      tokenOfSynthetic role kind value startPos stopPos
  | .none =>
      tokenOfNone role kind value

/-! ## Raw tree extraction -/

partial def extractRawTree (source : String) : Syntax → Tree
  | .missing => .missing
  | .atom info value =>
      .leaf <| tokenOfSourceInfo source .atom .anonymous value info
  | .ident info rawValue _ _ =>
      .leaf <| tokenOfSourceInfo source .ident Lean.identKind rawValue.toString info
  | .node _ kind children =>
      .node (.raw kind) <| children.map (extractRawTree source)

def tokenComesFromSource (source : String) (token : Token) : Bool :=
  token.span.start < token.span.stop
  && sourceText source token.span.start token.span.stop == token.lexeme

partial def removeOverlappingSourceTokensAux
    (source : String) (consumedUntil : String.Pos.Raw)
    : Tree → Tree × String.Pos.Raw
  | .missing => (.missing, consumedUntil)
  | .leaf token =>
      if tokenComesFromSource source token then
        if token.span.start < consumedUntil then
          (.missing, consumedUntil)
        else
          (.leaf token, token.span.stop)
      else
        (.leaf token, consumedUntil)
  | .node kind children =>
      let (children, consumedUntil) :=
        children.foldl
          (fun (filtered, consumedUntil) child =>
            let (child, consumedUntil) :=
              removeOverlappingSourceTokensAux source consumedUntil child
            (filtered.push child, consumedUntil))
          (#[], consumedUntil)
      let children :=
        if kind == .raw `choice then
          children.filter fun child => child.firstToken?.isSome
        else
          children
      (.node kind children, consumedUntil)

def removeOverlappingSourceTokens (source : String) (tree : Tree) : Tree :=
  (removeOverlappingSourceTokensAux source 0 tree).1

def rawKind? : Tree → Option SyntaxNodeKind
  | .node (.raw kind) _ => some kind
  | .node (.letExpression kind _) _ => some kind
  | _ => none

partial def isPatternLambdaArgument : Tree → Bool
  | .node .patternLambda _ => true
  | .node (.raw `null) children =>
      let content := children.filter fun child => child.firstToken?.isSome
      content.size == 1 && content[0]?.any isPatternLambdaArgument
  | .node (.raw `Lean.Parser.Term.explicit) children
  | .node (.raw `Lean.Parser.Term.explicitUniv) children =>
      children.back?.any isPatternLambdaArgument
  | _ => false

abbrev InfixPrecedenceMap := NameMap (Nat × Nat)

partial def parserDescrPrecedence? (kind : SyntaxNodeKind)
    : ParserDescr → Option (Nat × Nat)
  | .trailingNode nodeKind precedence leftPrecedence parser =>
      if nodeKind == kind then
        some (precedence, leftPrecedence)
      else
        parserDescrPrecedence? kind parser
  | .node _ _ parser
  | .unary _ parser =>
      parserDescrPrecedence? kind parser
  | .binary _ left right =>
      parserDescrPrecedence? kind left <|> parserDescrPrecedence? kind right
  | _ => none

unsafe def parserPrecedenceUnsafe
    (env : Environment) (options : Options) (kind : SyntaxNodeKind)
    : Option (Nat × Nat) :=
  match env.find? kind with
  | some info =>
      if info.type.isConstOf ``TrailingParserDescr then
        match env.evalConst ParserDescr options kind with
        | .ok parser => parserDescrPrecedence? kind parser
        | .error _ => none
      else
        none
  | none => none

@[implemented_by parserPrecedenceUnsafe]
opaque parserPrecedence
  (env : Environment) (options : Options) (kind : SyntaxNodeKind) : Option (Nat × Nat)

structure ParserPrecedenceFacts where
  checkedKinds : NameSet := {}
  infixPrecedences : InfixPrecedenceMap := {}

def ParserPrecedenceFacts.record
    (facts : ParserPrecedenceFacts)
    (env : Environment) (options : Options) (kind : SyntaxNodeKind)
    : ParserPrecedenceFacts :=
  if facts.checkedKinds.contains kind then
    facts
  else
    let infixPrecedences :=
      match parserPrecedence env options kind with
      | some precedence => facts.infixPrecedences.insert kind precedence
      | none => facts.infixPrecedences
    {
      checkedKinds := facts.checkedKinds.insert kind
      infixPrecedences
    }

partial def collectParserPrecedenceFacts
    (env : Environment) (options : Options)
    (stx : Syntax) (facts : ParserPrecedenceFacts := {})
    : ParserPrecedenceFacts :=
  match stx with
  | .missing
  | .atom ..
  | .ident .. => facts
  | .node _ kind children =>
      children.foldl
        (fun facts child =>
          collectParserPrecedenceFacts env options child facts)
        (facts.record env options kind)

/-! ## Logical regrouping -/

private partial def directLeafAtomToken? : Tree → Option Token
  | .leaf token => if token.role == .atom then some token else none
  | .node (.raw `null) children =>
      match children.toList with
      | [child] => directLeafAtomToken? child
      | _ => none
  | _ => none

def directLeafAtom? (tree : Tree) : Bool :=
  (directLeafAtomToken? tree).isSome

def isBinaryInfixRawNode (kind : SyntaxNodeKind) (children : Array Tree) : Bool :=
  let hasLeftOperand := children[0]?.any fun child => child.firstToken?.isSome
  let hasRightOperand := children[2]?.any fun child => child.firstToken?.isSome
  kind != `null
  && kind != `Lean.Parser.Term.app
  && children.size == 3
  && hasLeftOperand
  && hasRightOperand
  && match children[1]? with
      | some operator => directLeafAtom? operator
      | none => false

private def isIndexedInfixRawNode (kind : SyntaxNodeKind) (children : Array Tree)
    : Bool :=
  let hasLeftOperand := children[0]?.any fun child => child.firstToken?.isSome
  let hasIndex := children[2]?.any fun child => child.firstToken?.isSome
  let hasRightOperand := children[4]?.any fun child => child.firstToken?.isSome
  kind != `null
  && kind != `Lean.Parser.Term.app
  && children.size == 5
  && hasLeftOperand
  && hasIndex
  && hasRightOperand
  && match children[1]?, children[3]? with
      | some operator, some closing =>
          match directLeafAtomToken? operator, directLeafAtomToken? closing with
          | some operator, some closing =>
              operator.lexeme != "["
              && operator.lexeme.endsWith "["
              && closing.lexeme == "]"
          | _, _ => false
      | _, _ => false

def appendApplicationArgumentChildren (argumentContainer : Tree) : Array Tree :=
  match argumentContainer with
  | .node (.raw `null) children => children
  | child => #[child]

def infixKindsSharePrecedence
    (infixPrecedences : InfixPrecedenceMap)
    (left right : SyntaxNodeKind)
    : Bool :=
  left == right
  || match infixPrecedences.find? left, infixPrecedences.find? right with
      | some leftPrecedence, some rightPrecedence =>
          leftPrecedence == rightPrecedence
      | _, _ => false

def appendInfixParts
    (infixPrecedences : InfixPrecedenceMap)
    (kind : SyntaxNodeKind) (parts : Array Tree) (tree : Tree)
    : Array Tree :=
  match tree with
  | .node (.infixChain childKind) children =>
      if infixKindsSharePrecedence infixPrecedences kind childKind then
        parts ++ children
      else
        parts.push tree
  | _ => parts.push tree

def flattenLowPriorityInfixParts (parts : Array Tree) : Array Tree :=
  parts.flatMap
    fun
    | .node .lowPriorityInfixRhs children => children
    | child => #[child]

def regroupLowPriorityInfixRhs (parts : Array Tree) : Array Tree :=
  match parts.toList with
  | [] => #[]
  | first :: rest =>
      let rec loop : List Tree → List Tree
        | operator :: rhs :: rest =>
            .node .lowPriorityInfixRhs #[operator, rhs] :: loop rest
        | _ => []
      (first :: loop rest).toArray

def regroupSignatureParameters : Tree → Tree
  | .node (.raw `null) children => .node .signatureParameters children
  | tree => tree

def flattenDeclarationIdentifierChild : Tree → Array Tree
  | .node (.raw `Lean.Parser.Command.optDeclSig) children
  | .node (.raw `Lean.Parser.Command.declSig) children =>
      children.flatMap
        fun child =>
          match child with
          | .node .signatureParameters parameters => parameters
          | child => #[child]
  | child => #[child]

def regroupDeclarationIdentifierChildren (children : Array Tree) : Array Tree :=
  children.flatMap flattenDeclarationIdentifierChild

def regroupUnifHintChildren (children : Array Tree) : Array Tree :=
  let children :=
    match children[4]? with
    | some parameters => children.set! 4 (regroupSignatureParameters parameters)
    | none => children
  match children[6]? with
  | some (Tree.node (NodeKind.raw `null) constraints) =>
      children.set! 6 (.node .unifConstraints constraints)
  | _ => children

def regroupMatchPatterns : Tree → Tree
  | .node (.raw `null) children =>
      if children.size == 1 then
        match children[0]? with
        | some (Tree.node (.raw `null) nested) => .node .matchPatterns nested
        | _ => .node .matchPatterns children
      else
        .node .matchPatterns children
  | tree => tree

def regroupMatchDiscriminants : Tree → Tree
  | .node (.raw `null) children => .node .matchDiscriminants children
  | tree => .node .matchDiscriminants #[tree]

def previousContentIndex? (children : Array Tree) (index : Nat) : Option Nat :=
  (List.range index).foldl
    (fun found candidate =>
      match children[candidate]? >>= Tree.firstToken? with
      | some _ => some candidate
      | none => found)
    none

def unwrapSingleNullChild (children : Array Tree) : Array Tree :=
  if children.size == 1 then
    match children[0]? with
    | some (Tree.node (.raw `null) wrappedChildren) => wrappedChildren
    | _ => children
  else
    children

def childrenRange (children : Array Tree) (start stop : Nat) : Array Tree :=
  (List.range (stop - start)).foldl
    (fun acc offset =>
      match children[start + offset]? with
      | some child => acc.push child
      | none => acc)
    #[]

def appendApplicationArgumentContainers (children : Array Tree) (start : Nat)
    : Array Tree :=
  (childrenRange children start children.size).foldl
    (fun arguments container =>
      arguments ++ appendApplicationArgumentChildren container)
    #[]

partial def structInstFieldParts? : Tree → Option (Array Tree)
  | .node (.raw `Lean.Parser.Term.structInstFieldDef) children => some children
  | .node _ children =>
      let rec loop (index : Nat)
          : Option (Array Tree) := do
        let child ← children[index]?
        match structInstFieldParts? child with
        | some parts =>
            some
            <| childrenRange children 0 index
                ++ parts
                ++ childrenRange children (index + 1) children.size
        | none => loop (index + 1)
      loop 0
  | _ => none

def doForDeclChildren? : Tree → Option (Array Tree)
  | .node (.raw `Lean.Parser.Term.doForDecl) children => some children
  | .node (.raw `null) children =>
      match children.toList with
      | [.node (.raw `Lean.Parser.Term.doForDecl) children] => some children
      | _ => none
  | _ => none

def regroupDoForChildren (children : Array Tree) : Option (Array Tree) := do
  let keyword ← children[0]?
  let declaration ← children[1]?
  let declarationChildren ← doForDeclChildren? declaration
  some
  <| #[.node .doForHeader (#[keyword] ++ declarationChildren)]
      ++ childrenRange children 2 children.size

def regroupLetEquationSignature (children : Array Tree) : Option (Array Tree) := do
  let name ← children[0]?
  let parameters ← children[1]?
  let typeSpec ← children[2]?
  some
  <| #[
        name,
        .node (.raw `Lean.Parser.Command.optDeclSig)
          #[regroupSignatureParameters parameters, typeSpec]
      ]
      ++ childrenRange children 3 children.size

partial def isDocCommentContainer : Tree → Bool
  | .node (.raw `Lean.Parser.Command.docComment) _ => true
  | .node kind children =>
      if kind == .raw `null || kind == .raw `Lean.Parser.Command.declModifiers then
        let presentChildren := children.filter fun child => child.firstToken?.isSome
        !presentChildren.isEmpty && presentChildren.all isDocCommentContainer
      else
        false
  | _ => false

def regroupLetRecDeclAnnotations (children : Array Tree) : Option (Array Tree) := do
  let annotationsIndex ←
    (children.findIdx?
      fun child => child.firstToken?.map (fun token => token.lexeme) == some "@[")
    |>.orElse fun _ => children.findIdx? isDocCommentContainer
  let declarationIndex ←
    children.findIdx?
      fun child =>
        rawKind? child == some `Lean.Parser.Term.letDecl
  if declarationIndex <= annotationsIndex then
    none
  else
    let annotationsContainer ← children[annotationsIndex]?
    let annotations :=
      match annotationsContainer with
      | .node (.raw `null) wrappedChildren =>
          if wrappedChildren.size == 1 then
            match wrappedChildren[0]? with
            | some annotations => annotations
            | none => annotationsContainer
          else
            annotationsContainer
      | _ => annotationsContainer
    let declaration ← children[declarationIndex]?
    some
    <| (children.set! annotationsIndex
          (.node .annotatedDeclaration #[annotations, declaration])).set!
        declarationIndex .missing

partial def lakeConfigChildren? : Tree → Option (Array Tree)
  | .node (.raw `Lake.DSL.declValWhere) children => some children
  | .node _ children =>
      children.foldl
        (fun found child =>
          match found with
          | some children => some children
          | none => lakeConfigChildren? child)
        none
  | _ => none

def regroupLakeCommandChildren (children : Array Tree) : Array Tree :=
  children.foldl
    (fun regrouped child =>
      if rawKind? child == some `Lake.DSL.optConfig then
        match lakeConfigChildren? child with
        | some configChildren => regrouped ++ configChildren
        | none => regrouped.push child
      else
        regrouped.push child)
    #[]

partial def flattenLakeRequireTree : Tree → Array Tree
  | .missing => #[]
  | tree@(.node (.raw kind) children) =>
      if kind == `null
          || kind == `Lake.DSL.depSpec
          || kind == `Lake.DSL.depName
          || kind == `Lake.DSL.identOrStr
          || kind == `Lake.DSL.fromClause
          || kind == `Lake.DSL.fromSource
          || kind == `Lake.DSL.fromGit then
        children.foldl
          (fun flattened child => flattened ++ flattenLakeRequireTree child) #[]
      else
        #[tree]
  | tree => #[tree]

def regroupLakeRequireChildren (children : Array Tree) : Array Tree :=
  children.foldl (fun flattened child => flattened ++ flattenLakeRequireTree child) #[]

def unwrapSingleNullTree : Tree → Tree
  | tree@(.node (.raw `null) children) =>
      if children.size == 1 then children[0]?.getD tree else tree
  | tree => tree

def splitWhereStructInstTrailingWhereDecls? : Tree → Option (Tree × Tree)
  | .node (.raw `Lean.Parser.Command.whereStructInst) children => do
      let trailingIndex ←
        children.findIdx?
          fun child =>
            rawKind? (unwrapSingleNullTree child) == some `Lean.Parser.Term.whereDecls
      let trailing ← children[trailingIndex]?
      some
        (
          .node (.raw `Lean.Parser.Command.whereStructInst)
            (children.set! trailingIndex .missing),
          unwrapSingleNullTree trailing
        )
  | _ => none

def regroupDefinitionTrailingWhereDecls? (children : Array Tree) : Option (Array Tree) :=
  match children.findIdx?
          fun child =>
            (splitWhereStructInstTrailingWhereDecls? child).isSome with
  | some valueIndex =>
      match children[valueIndex]? >>= splitWhereStructInstTrailingWhereDecls? with
      | some (value, trailing) =>
          some
          <| childrenRange children 0 valueIndex
              ++ #[value, trailing]
              ++ childrenRange children (valueIndex + 1) children.size
      | none => none
  | none => none

def flattenSimpleDeclarationValueChildren? (children : Array Tree)
    : Option (Array Tree) := do
  let valueIndex ←
    children.findIdx?
      fun child => rawKind? child == some `Lean.Parser.Command.declValSimple
  let value ← children[valueIndex]?
  match value with
  | .node _ valueChildren =>
      some
      <| childrenRange children 0 valueIndex
          ++ valueChildren
          ++ childrenRange children (valueIndex + 1) children.size
  | _ => none

def regroupFlattenedDefinitionChildren (children : Array Tree) : Array Tree :=
  (regroupDefinitionTrailingWhereDecls? children).getD children

def regroupDefinitionChildren (children : Array Tree) : Option (Array Tree) :=
  match flattenSimpleDeclarationValueChildren? children with
  | some flattened =>
      some <| regroupFlattenedDefinitionChildren flattened
  | none =>
      match regroupDefinitionTrailingWhereDecls? children with
      | some children => some children
      | none =>
          if children.any
              fun child =>
                rawKind? child == some `Lean.Parser.Command.whereStructInst then
            some children
          else
            none

def splitEquationTrailingClauses? : Tree → Option (Tree × Array Tree)
  | .node (.raw `Lean.Parser.Command.declValEqns) valueChildren => do
      let alternativesIndex ←
        valueChildren.findIdx?
          fun child =>
            rawKind? child == some `Lean.Parser.Term.matchAltsWhereDecls
      let alternatives ← valueChildren[alternativesIndex]?
      match alternatives with
      | .node (.raw `Lean.Parser.Term.matchAltsWhereDecls) children => do
          let clauseIndexes :=
            (List.range children.size).filter
              fun index =>
                match children[index]? with
                | some child =>
                    (rawKind? child == some `Lean.Parser.Termination.suffix
                      && child.firstToken?.isSome)
                    || child.firstToken?.any fun token => token.lexeme == "where"
                | none => false
          let firstClauseIndex ← clauseIndexes.head?
          if !(childrenRange children 0 firstClauseIndex).any
                fun child => child.firstToken?.any fun token => token.lexeme == "|" then
            none
          let clauses :=
            clauseIndexes.foldl
              (fun clauses index =>
                match children[index]? with
                | some child =>
                    clauses.push
                    <|  if child.firstToken?.any fun token => token.lexeme == "where" then
                          unwrapSingleNullTree child
                        else
                          child
                | none => clauses)
              #[]
          let alternatives :=
            .node (.raw `Lean.Parser.Term.matchAltsWhereDecls)
              (children.mapIdx
                fun index child =>
                  if clauseIndexes.contains index then .missing else child)
          let value :=
            .node (.raw `Lean.Parser.Command.declValEqns)
              (valueChildren.set! alternativesIndex alternatives)
          some (value, clauses)
      | _ => none
  | _ => none

def regroupEquationTrailingClauseChildren (children : Array Tree) : Array Tree :=
  match children[3]? >>= splitEquationTrailingClauses? with
  | some (value, clauses) =>
      childrenRange children 0 3
      ++ #[value]
      ++ clauses
      ++ childrenRange children 4 children.size
  | none => children

def declarationValueCommandKind (kind : SyntaxNodeKind) : Bool :=
  kind == `Lean.Parser.Command.theorem || kind == `lemma || kind == `group

def splitLeadingAnnotations? : Tree → Option (Tree × Tree)
  | .node (.raw `Lean.Parser.Command.declModifiers) children => do
      let reverseIndex ←
        children.reverse.findIdx?
          fun child =>
            child.firstToken?.map (fun token => token.lexeme) == some "@["
            || isDocCommentContainer child
      let annotationIndex := children.size - reverseIndex - 1
      let annotation ← children[annotationIndex]?
      let annotationChildren :=
        children.mapIdx
          fun index child =>
            if index < annotationIndex then
              child
            else if index == annotationIndex then
              annotation
            else
              .missing
      let remainingChildren :=
        children.mapIdx
          fun index child =>
            if annotationIndex < index then child else .missing
      some
        (
          .node (.raw `Lean.Parser.Command.declModifiers) annotationChildren,
          .node (.raw `Lean.Parser.Command.declModifiers) remainingChildren
        )
  | _ => none

def splitDeclarationAnnotations? : Tree → Option (Tree × Tree)
  | .node kind children => do
      match children.findIdx?
              fun child =>
                rawKind? child == some `Lean.Parser.Command.declModifiers with
      | some modifierIndex => do
          let modifiers ← children[modifierIndex]?
          let (annotations, remainingModifiers) ← splitLeadingAnnotations? modifiers
          some (annotations, .node kind (children.set! modifierIndex remainingModifiers))
      | none => do
          if kind == .raw `null then
            none
          let annotationIndex ←
            children.findIdx?
              fun child =>
                child.firstToken?.map (fun token => token.lexeme) == some "@["
                && child.lastToken?.map (fun token => token.lexeme) == some "]"
          if (previousContentIndex? children annotationIndex).isSome then
            none
          else
            let annotations ← children[annotationIndex]?
            some (annotations, .node kind (children.set! annotationIndex .missing))
  | _ => none

def splitLeadingDeclarationModifiers? : Tree → Option (Tree × Tree)
  | .node kind children => do
      let modifierIndex ←
        children.findIdx?
          fun child =>
            rawKind? child == some `Lean.Parser.Command.declModifiers
      if (previousContentIndex? children modifierIndex).isSome then
        none
      else
        let modifiers ← children[modifierIndex]?
        if modifiers.firstToken?.isSome then
          some
            (
              modifiers,
              .node kind
                (childrenRange children 0 modifierIndex
                  ++ childrenRange children (modifierIndex + 1) children.size)
            )
        else
          none
  | _ => none

def splitDirectCommandDocComment? : Tree → Option (Tree × Tree)
  | .node kind children => do
      let annotationIndex ←
        children.findIdx?
          fun child =>
            child.firstToken?.isSome
      let annotation ← children[annotationIndex]?
      if isDocCommentContainer annotation then
        some (annotation, .node kind (children.set! annotationIndex .missing))
      else
        none
  | _ => none

def annotatedDeclarationTree (annotations modifiers declaration : Tree) : Tree :=
  let children :=
    if modifiers.firstToken?.isSome then
      #[annotations, modifiers, declaration]
    else
      #[annotations, declaration]
  .node .annotatedDeclaration children

def annotatedDeclarationTreeForCommand (annotations command : Tree) : Tree :=
  match splitLeadingDeclarationModifiers? command with
  | some (modifiers, command) =>
      annotatedDeclarationTree annotations modifiers command
  | none => annotatedDeclarationTree annotations .missing command

def regroupStructCtor (children : Array Tree) : Tree :=
  let command := .node (.raw `Lean.Parser.Command.structCtor) (children.set! 0 .missing)
  match children[0]? with
  | some modifiers =>
      match splitLeadingAnnotations? modifiers with
      | some (annotations, remainingModifiers) =>
          annotatedDeclarationTree annotations remainingModifiers command
      | none =>
          if modifiers.firstToken?.isSome then
            .node .annotatedDeclaration #[modifiers, command]
          else
            command
  | none => command

def regroupCtor (children : Array Tree) : Tree :=
  match children[2]? with
  | some modifiers =>
      match splitLeadingAnnotations? modifiers with
      | some (annotations, remainingModifiers) =>
          let command :=
            .node (.raw `Lean.Parser.Command.ctor)
            <| ((children.set! 0 .missing).set! 1 .missing).set! 2 .missing
          .node (.raw `Lean.Parser.Command.ctor)
          <| childrenRange children 0 2
              ++ #[annotatedDeclarationTree annotations remainingModifiers command]
      | none =>
          .node (.raw `Lean.Parser.Command.ctor) children
  | none =>
      .node (.raw `Lean.Parser.Command.ctor) children

def regroupStructure (children : Array Tree) : Tree :=
  let trailingDeriving :=
    match children[5]? with
    | some clause =>
        if clause.firstToken?.isSome then
          #[.node .structureDeriving #[clause]]
        else
          #[]
    | none => #[]
  match children[4]? with
  | some (Tree.node (.raw `null) whereChildren) =>
      match whereChildren[0]? with
      | some whereKeyword =>
          let header :=
            .node .structureHeader (childrenRange children 0 4 ++ #[whereKeyword])
          let constructor :=
            match whereChildren[1]? with
            | some (Tree.node (.raw `null) declarations) =>
                if declarations.any fun child => child.firstToken?.isSome then
                  #[.node .structureConstructor declarations]
                else
                  #[]
            | some declaration =>
                if declaration.firstToken?.isSome then
                  #[.node .structureConstructor #[declaration]]
                else
                  #[]
            | none => #[]
          let fields :=
            match whereChildren[2]? with
            | some fields =>
                if fields.firstToken?.isSome then #[fields] else #[]
            | none => #[]
          .node (.raw `Lean.Parser.Command.structure)
          <| #[header]
              ++ constructor
              ++ fields
              ++ childrenRange whereChildren 3 whereChildren.size
              ++ trailingDeriving
              ++ childrenRange children 6 children.size
      | none =>
          .node (.raw `Lean.Parser.Command.structure)
          <| #[.node .structureHeader (childrenRange children 0 4)]
              ++ trailingDeriving
              ++ childrenRange children 6 children.size
  | _ => .node (.raw `Lean.Parser.Command.structure) children

def regroupDeclarationValueCommand (kind : SyntaxNodeKind) (children : Array Tree)
    : Tree :=
  let children := regroupEquationTrailingClauseChildren children
  let command :=
    match regroupDefinitionChildren children with
    | some declarationChildren => .node (.raw kind) declarationChildren
    | none => .node (.raw kind) children
  match splitDeclarationAnnotations? command with
  | some (annotations, command) =>
      annotatedDeclarationTreeForCommand annotations command
  | none => command

def regroupDeclarationChildren (children : Array Tree) : Option (Array Tree) := do
  let modifiers ← children[0]?
  let declaration ← children[1]?
  let annotatedDeclaration? : Option Tree :=
    match splitLeadingAnnotations? modifiers with
    | some (annotations, remainingModifiers) =>
        some <| annotatedDeclarationTree annotations remainingModifiers declaration
    | none =>
        match splitDeclarationAnnotations? declaration with
        | some (annotations, declaration) =>
            some <| annotatedDeclarationTree annotations modifiers declaration
        | none =>
            if (Tree.firstToken? modifiers).isSome then
              some <| Tree.node .annotatedDeclaration #[modifiers, declaration]
            else
              none
  annotatedDeclaration?.map
    fun annotatedDeclaration =>
      #[annotatedDeclaration] ++ childrenRange children 2 children.size

partial def structureUpdateSourceChildren : Tree → Array Tree
  | .node (.raw `null) children =>
      children.foldl
        (fun flattened child => flattened ++ structureUpdateSourceChildren child) #[]
  | tree => #[tree]

def regroupStructureUpdateSource (tree : Tree) : Tree :=
  .node .structureUpdate (structureUpdateSourceChildren tree)

def regroupStructInstChildren (children : Array Tree) : Array Tree :=
  match children[1]? with
  | some source =>
      if source.lastToken?.map (·.lexeme) == some "with" then
        children.set! 1 (regroupStructureUpdateSource source)
      else
        children
  | none => children

def regroupRegisterLinterSetChildren (children : Array Tree) : Array Tree :=
  match (children[4]? : Option Tree) with
  | some (.node (.raw `null) items) =>
      childrenRange children 0 4 ++ items ++ childrenRange children 5 children.size
  | _ => children

def regroupDoFallbackChildren? (children : Array Tree) : Option (Array Tree) := do
  let pipeIndex ←
    children.findIdx?
      fun child => child.firstToken?.map (fun token => token.lexeme) == some "|"
  let fallbackIndex ←
    (List.range' (pipeIndex + 1) (children.size - pipeIndex - 1)).find?
      fun index => children[index]?.any fun child => child.firstToken?.isSome
  let pipe ← children[pipeIndex]?
  let fallback ← children[fallbackIndex]?
  let clause := .node .doFallbackClause #[pipe, fallback]
  let continuationChildren := childrenRange children (fallbackIndex + 1) children.size
  let continuation :=
    if continuationChildren.isEmpty then
      #[]
    else
      #[.node .doFallbackContinuation continuationChildren]
  some <| childrenRange children 0 pipeIndex ++ #[clause] ++ continuation

def regroupDoDeclarationFallbackChildren (children : Array Tree) : Array Tree :=
  children.foldl
    (fun regrouped child =>
      match child with
      | .node (.raw `null) fallbackChildren =>
          match regroupDoFallbackChildren? fallbackChildren with
          | some grouped => regrouped ++ grouped
          | none => regrouped.push child
      | _ => regrouped.push child)
    #[]

def isIfThenElseKind (kind : SyntaxNodeKind) : Bool :=
  kind == `termIfThenElse || kind == `boolIfThenElse

def ifThenElseChainParts? : Tree → Option (Array Tree)
  | .node (.raw kind) children => do
      if !isIfThenElseKind kind || children.size != 6 then
        none
      let thenBranch ← children[3]?
      let elseKeyword ← children[4]?
      let elseBranch ← children[5]?
      some
        #[
          .node .ifThenElseClause (childrenRange children 0 3),
          thenBranch,
          elseKeyword,
          elseBranch
        ]
  | .node .ifThenElseChain children => some children
  | _ => none

def prependElseToIfThenElseClause (elseKeyword : Tree) (parts : Array Tree)
    : Option (Array Tree) := do
  let first ← parts[0]?
  match first with
  | .node .ifThenElseClause children =>
      some <| parts.set! 0 (.node .ifThenElseClause (#[elseKeyword] ++ children))
  | _ => none

def regroupIfThenElseChain (kind : SyntaxNodeKind) (children : Array Tree) : Tree :=
  let chain? : Option Tree := do
    let thenBranch ← children[3]?
    let elseKeyword ← children[4]?
    let elseBranch ← children[5]?
    let continuation ← ifThenElseChainParts? elseBranch
    let continuation ← prependElseToIfThenElseClause elseKeyword continuation
    some
    <| .node .ifThenElseChain
    <| #[.node .ifThenElseClause (childrenRange children 0 3), thenBranch] ++ continuation
  chain?.getD <| .node (.raw kind) children

def proofBodyTree (children : Array Tree) : Tree :=
  .node (.proofBody <| children.any Tree.containsTacticLayoutOwner) children

def regroupByTacticChildren (children : Array Tree) : Array Tree :=
  match children[0]? with
  | some byKeyword =>
      #[byKeyword, proofBodyTree <| childrenRange children 1 children.size]
  | none => children

def regroupDecreasingByChildren (children : Array Tree) : Array Tree :=
  match children[0]? with
  | some decreasingByKeyword =>
      #[decreasingByKeyword, proofBodyTree <| childrenRange children 1 children.size]
  | none => children

def regroupTerminationByParameters (parameters arrow : Tree) : Tree :=
  match parameters with
  | .node (.raw `null) parameterChildren =>
      match parameterChildren.back? with
      | some finalParameter =>
          .node .signatureParameters
          <| childrenRange parameterChildren 0 (parameterChildren.size - 1)
              ++ #[.node (.raw `null) #[finalParameter, arrow]]
      | none => .node .signatureParameters #[arrow]
  | _ =>
      .node .signatureParameters #[.node (.raw `null) #[parameters, arrow]]

def regroupTerminationByChildren (children : Array Tree) : Array Tree :=
  match children.findIdx?
          fun child =>
            match child with
            | .node (.raw `null) parts =>
                parts.size == 2
                && parts[1]?.any
                    fun arrow => arrow.firstToken?.any fun token => token.lexeme == "=>"
            | _ => false with
  | some parameterArrowIndex =>
      match children[parameterArrowIndex]? with
      | some (.node (.raw `null) parameterArrowParts) =>
          match parameterArrowParts[0]?, parameterArrowParts[1]? with
          | some parameters, some arrow =>
              childrenRange children 0 parameterArrowIndex
              ++ #[regroupTerminationByParameters parameters arrow]
              ++ childrenRange children (parameterArrowIndex + 1) children.size
          | _, _ => children
      | _ => children
  | none => children

def regroupTerminationSuffixChildren (children : Array Tree) : Array Tree :=
  children.foldl
    (fun clauses child =>
      let clause := unwrapSingleNullTree child
      if clause.firstToken?.isSome then clauses.push clause else clauses)
    #[]

def regroupWhereFinallyChildren (children : Array Tree) : Array Tree :=
  match children[1]? with
  | some tacticBody =>
      children.set! 1 <| proofBodyTree #[tacticBody]
  | none => children

def regroupWhereDeclsChildren (children : Array Tree) : Array Tree :=
  match children[0]?, children[1]?, children[2]? with
  | some whereKeyword,
    some (Tree.node (.raw `null) declarations),
    some (Tree.node (.raw `null) finallyWrapper) =>
      let finallyChildren :=
        match finallyWrapper[0]? with
        | some (Tree.node (.raw `Lean.Parser.Term.whereFinally) children) =>
            if finallyWrapper.size == 1 then children else finallyWrapper
        | _ => finallyWrapper
      #[whereKeyword] ++ declarations ++ finallyChildren
  | _, _, _ => children

def regroupCommandInWrapperChildren (children : Array Tree) : Array Tree :=
  match children[1]? with
  | some (Tree.node (.raw `null) wrapped) =>
      match wrapped[0]? with
      | some first =>
          if first.firstToken?.any (·.lexeme == "in") then
            childrenRange children 0 1
            ++ wrapped
            ++ childrenRange children 2 children.size
          else
            children
      | none => children
  | _ => children

def regroupBinderTacticChildren (children : Array Tree) : Array Tree :=
  match children[0]?, children[1]? with
  | some assignment, some byKeyword =>
      #[assignment, byKeyword, proofBodyTree <| childrenRange children 2 children.size]
  | _, _ => children

def singleContentChild? (children : Array Tree) : Option Tree :=
  let content := children.filter fun child => child.firstToken?.isSome
  if content.size == 1 then content[0]? else none

partial def attachedDoTree? : Tree → Option Tree
  | tree@(.node (.raw `Lean.Parser.Term.doNested) _) => some tree
  | .node (.raw kind) children =>
      if kind == `Lean.Parser.Term.doSeqIndent
          || kind == `Lean.Parser.Term.doSeqItem
          || kind == `null then
        singleContentChild? children >>= attachedDoTree?
      else
        none
  | _ => none

def regroupAttachedDoRhs (children : Array Tree) : Array Tree :=
  match children[3]? >>= attachedDoTree? with
  | some body => children.set! 3 body
  | none => children

def regroupDerivingClause? (children : Array Tree) : Option Tree := do
  let keyword ← children[0]?
  if keyword.firstToken?.map (·.lexeme) != some "deriving" then
    none
  let classes ← children[1]?
  match classes with
  | .node (.raw `null) classChildren =>
      some <| .node .derivingClause (#[keyword] ++ classChildren)
  | _ => none

def regroupDerivingCommandChildren (children : Array Tree) : Array Tree :=
  match (children[3]? : Option Tree) with
  | some (.node (.raw `null) classChildren) =>
      children.set! 3 (.node .derivingClause classChildren)
  | _ => children

def isDelimitedCollectionKind (kind : SyntaxNodeKind) : Bool :=
  kind == `Lean.Parser.Term.tuple
  || kind == `Lean.Parser.Term.anonymousCtor
  || kind == `«term{_}»
  || kind == `«term[_]»
  || kind == `«term#[_,]»
  || kind == `Matrix.vecNotation
  || kind == `Matrix.matrixNotation

partial def flattenDelimitedCollectionChildren (children : Array Tree) : Array Tree :=
  match children.findIdx? fun child => rawKind? child == some `null with
  | some index =>
      match children[index]? with
      | some (.node (.raw `null) items) =>
          let hasSeparator :=
            items.any
              fun item =>
                item.firstToken?.any
                  fun token =>
                    token.lexeme == "," || token.lexeme == ";"
          if hasSeparator then
            flattenDelimitedCollectionChildren
            <| childrenRange children 0 index
                ++ items
                ++ childrenRange children (index + 1) children.size
          else
            children
      | _ => children
  | none => children

def regroupOtherRawNode (kind : SyntaxNodeKind) (children : Array Tree) : Tree :=
  if kind == `Lean.Parser.Command.deriving then
    .node (.raw kind) (regroupDerivingCommandChildren children)
  else if kind == `Lean.Parser.Command.declaration then
    match regroupDeclarationChildren children with
    | some declarationChildren => .node (.raw kind) declarationChildren
    | none => .node (.raw kind) children
  else if kind == `Lean.Parser.Term.doIdDecl || kind == `Lean.Parser.Term.doPatDecl then
    .node (.raw kind) (regroupDoDeclarationFallbackChildren children)
  else if kind == `Lean.Parser.Term.doLetElse || kind == `Lean.Parser.Term.doLetExpr then
    match regroupDoFallbackChildren? children with
    | some grouped => .node (.raw kind) grouped
    | none => .node (.raw kind) children
  else if kind == `Lean.Parser.Term.structInst then
    .node (.raw kind) (regroupStructInstChildren children)
  else if kind == `Lean.Parser.Command.optDeclSig
          || kind == `Lean.Parser.Command.declSig then
    match children[0]?, children[1]? with
    | some parameters, some typeSpec =>
        .node (.raw kind) #[regroupSignatureParameters parameters, typeSpec]
    | _, _ =>
        .node (.raw kind) children
  else if kind == `Lean.Parser.Command.declId then
    .node (.raw kind) (regroupDeclarationIdentifierChildren children)
  else if kind == `Lean.Parser.Command.structCtor then
    regroupStructCtor children
  else if kind == `Lean.Parser.Command.ctor then
    regroupCtor children
  else if kind == `Lean.Parser.Command.structure then
    regroupStructure children
  else if kind == `Lean.Parser.Term.fun
          && children.any
              fun child => rawKind? child == some `Lean.Parser.Term.matchAlts then
    .node .patternLambda children
  else if kind == `Lean.Parser.Term.basicFun then
    match children[0]? with
    | some parameters =>
        .node (.raw kind) <| children.set! 0 (regroupSignatureParameters parameters)
    | none => .node (.raw kind) children
  else if kind == `Lean.«command__Unif_hint____Where_|_-⊢__» then
    .node (.raw kind) (regroupUnifHintChildren children)
  else if kind == `Lean.Parser.Term.letEqnsDecl then
    match regroupLetEquationSignature children with
    | some children => .node (.raw kind) children
    | none => .node (.raw kind) children
  else if kind == `Lean.Parser.Term.letIdDecl then
    match children[1]? with
    | some parameters =>
        .node (.raw kind) <| children.set! 1 (regroupSignatureParameters parameters)
    | none => .node (.raw kind) children
  else if kind == `Lean.Parser.Term.letRecDecl then
    match regroupLetRecDeclAnnotations children with
    | some children => .node (.raw kind) children
    | none => .node (.raw kind) children
  else if kind == `Lean.Parser.Term.matchAlt then
    let children := regroupAttachedDoRhs children
    match children[1]? with
    | some patterns =>
        .node (.raw kind) <| children.set! 1 (regroupMatchPatterns patterns)
    | none => .node (.raw kind) children
  else if kind == `Lean.Parser.Term.doIf then
    .node (.raw kind) (regroupAttachedDoRhs children)
  else if kind == `Lean.Parser.Term.structInstField then
    match children[0]?, children[1]? >>= structInstFieldParts? with
    | some lvalue, some fieldParts =>
        let fieldParts :=
          match fieldParts[0]? with
          | some parameters =>
              fieldParts.set! 0 (regroupSignatureParameters parameters)
          | none => fieldParts
        .node (.raw kind) <| #[lvalue] ++ fieldParts
    | _, _ => .node (.raw kind) children
  else if kind == `Lean.Parser.Term.match then
    match children.findIdx?
            fun child =>
              (Tree.firstToken? child).map (fun token => token.lexeme) == some "with" with
    | some withIndex =>
        match previousContentIndex? children withIndex with
        | some discriminantsIndex =>
            match children[discriminantsIndex]? with
            | some discriminants =>
                .node (.raw kind)
                <| children.set! discriminantsIndex
                    (regroupMatchDiscriminants discriminants)
            | none => .node (.raw kind) children
        | none => .node (.raw kind) children
    | none => .node (.raw kind) children
  else if kind == `Lean.Parser.Term.matchAlts then
    .node (.raw kind) (unwrapSingleNullChild children)
  else if kind == `Lean.Parser.Term.doFor then
    match regroupDoForChildren children with
    | some children => .node (.raw kind) children
    | none => .node (.raw kind) children
  else if kind == `Lean.Parser.Term.byTactic || kind == `Lean.Parser.Term.byTactic' then
    .node (.raw kind) (regroupByTacticChildren children)
  else if kind == `Lean.Parser.Termination.decreasingBy then
    .node (.raw kind) (regroupDecreasingByChildren children)
  else if kind == `Lean.Parser.Termination.terminationBy then
    .node (.raw kind) (regroupTerminationByChildren children)
  else if kind == `Lean.Parser.Termination.suffix then
    .node (.raw kind) (regroupTerminationSuffixChildren children)
  else if kind == `Lean.Parser.Term.whereFinally then
    .node (.raw kind) (regroupWhereFinallyChildren children)
  else if kind == `Lean.Parser.Term.whereDecls then
    .node (.raw kind) (regroupWhereDeclsChildren children)
  else if kind == `Lean.Parser.Command.declModifiers then
    .node (.raw kind) children
  else
    let tree := .node (.raw kind) children
    if tree.firstToken?.map (fun token => token.lexeme) == some "@["
        && tree.lastToken?.map (fun token => token.lexeme) == some "]" then
      tree
    else
      match splitDeclarationAnnotations? tree with
      | some (annotations, command) =>
          annotatedDeclarationTreeForCommand annotations command
      | none =>
          match splitDirectCommandDocComment? tree with
          | some (annotations, command) =>
              annotatedDeclarationTreeForCommand annotations command
          | none =>
              match splitLeadingDeclarationModifiers? tree with
              | some (modifiers, command) =>
                  .node .annotatedDeclaration #[modifiers, command]
              | none => tree

private def nodeKindHasRawKind (expected : SyntaxNodeKind) : NodeKind → Bool
  | .raw kind | .tactic kind _ _ _ => kind == expected
  | _ => false

private partial def treeIsCasesAlternativeGroup : Tree → Bool
  | .node kind children =>
      if nodeKindHasRawKind `Lean.Parser.Tactic.inductionAlt kind then
        true
      else
        match kind with
        | .raw `null =>
            let content := children.filter fun child => child.firstToken?.isSome
            !content.isEmpty && content.all treeIsCasesAlternativeGroup
        | _ => false
  | _ => false

private partial def casesTargetGroupContainsNamedDiscriminant : Tree → Bool
  | .node .namedDiscriminant _ => true
  | .node (.raw `null) children =>
      children.any casesTargetGroupContainsNamedDiscriminant
  | _ => false

def splitCasesDefaultAlternative? (alternatives : Tree) : Option (Tree × Tree) := do
  let .node kind children := unwrapSingleNullTree alternatives | none
  if !nodeKindHasRawKind `Lean.Parser.Tactic.inductionAlts kind then
    none
  else
    let contentIndexes :=
      (List.range children.size).filter
        fun index => children[index]?.any fun child => child.firstToken?.isSome
    let defaultIndex ← contentIndexes.head?
    let defaultAlternative ← children[defaultIndex]?
    if treeIsCasesAlternativeGroup defaultAlternative then
      none
    else
      let explicitAlternatives := .node kind (children.set! defaultIndex .missing)
      let defaultBody :=
        .node (.proofBody defaultAlternative.containsTacticLayoutOwner)
          #[defaultAlternative]
      some (defaultBody, explicitAlternatives)

def regroupCasesChildren (children : Array Tree) : Option (Array Tree) := do
  let alternativesIndex ←
    children.findIdx?
      fun child =>
        child.firstToken?.any fun token => token.lexeme == "with"
  let suffixIndex ← previousContentIndex? children alternativesIndex
  let headerContent := childrenRange children 0 alternativesIndex
  let headerContentIndexes :=
    (List.range headerContent.size).filter
      fun index => headerContent[index]?.any fun child => child.firstToken?.isSome
  let targetIndex ← headerContentIndexes[1]?
  let target ← headerContent[targetIndex]?
  let targetIsNamed := casesTargetGroupContainsNamedDiscriminant target
  let targetGroup :=
    match target with
    | .node (.raw `null) targetChildren =>
        .node (.tacticEliminationTargets targetIsNamed) targetChildren
    | _ => .node (.tacticEliminationTargets targetIsNamed) #[target]
  let children := children.set! targetIndex targetGroup
  let suffix ← children[suffixIndex]?
  let alternatives ← children[alternativesIndex]?
  let (withKeyword, alternatives) ← Tree.extractLeadingLexeme? "with" alternatives
  let suffix := .node .suffixGroup #[suffix, withKeyword]
  let children := children.set! suffixIndex suffix
  let headerChildren := childrenRange children 0 alternativesIndex
  let trailingChildren := childrenRange children (alternativesIndex + 1) children.size
  match splitCasesDefaultAlternative? alternatives with
  | some (defaultAlternative, explicitAlternatives) =>
      let header :=
        .node (.tacticEliminationHeader targetIsNamed)
          (headerChildren.push defaultAlternative)
      some <| #[header, explicitAlternatives] ++ trailingChildren
  | none =>
      let header := .node (.tacticEliminationHeader targetIsNamed) headerChildren
      some <| #[header, alternatives] ++ trailingChildren

def regroupNamedDiscriminant? (children : Array Tree) : Option Tree :=
  if children.size == 2 then do
    let nameAndColon ← children[0]?
    let discriminant ← children[1]?
    let (name, colon) ← Tree.extractTrailingLexeme? ":" nameAndColon
    if name.firstToken?.isNone || discriminant.firstToken?.isNone then
      none
    else
      some <| .node .namedDiscriminant #[name, colon, discriminant]
  else
    none

def regroupRawNode
    (infixPrecedences : InfixPrecedenceMap)
    (kind : SyntaxNodeKind) (children : Array Tree)
    : Tree :=
  if kind == `null then
    (regroupDerivingClause? children).getD <| .node (.raw kind) children
  else if kind == `Lean.Parser.Tactic.elimTarget then
    (regroupNamedDiscriminant? children).getD <| .node (.raw kind) children
  else if kind == `Lean.Parser.Tactic.cases then
    .node (.raw kind) ((regroupCasesChildren children).getD children)
  else if isIfThenElseKind kind then
    regroupIfThenElseChain kind children
  else if kind == `Lean.Parser.Term.app && children.size == 2 then
    match children[0]?, children[1]? with
    | some head, some argumentContainer =>
        let headAndArgs :=
          match head with
          | .node .application headChildren => headChildren
          | _ => #[head]
        .node .application
          (headAndArgs ++ appendApplicationArgumentChildren argumentContainer)
    | _, _ =>
        .node (.raw kind) children
  else if kind == `Lean.Parser.Term.pipeProj && 2 < children.size then
    match children[0]?, children[1]?, children[2]? with
    | some receiver, some operator, some head =>
        let right :=
          if children.size == 3 then
            head
          else
            .node .application (#[head] ++ appendApplicationArgumentContainers children 3)
        let parts := appendInfixParts infixPrecedences kind #[] receiver
        .node (.infixChain kind) <| parts.push operator |>.push right
    | _, _, _ => .node (.raw kind) children
  else if kind == `Lake.DSL.packageCommand || kind == `Lake.DSL.leanLibCommand then
    .node (.raw kind) (regroupLakeCommandChildren children)
  else if kind == `Lake.DSL.requireDecl then
    .node (.raw kind) (regroupLakeRequireChildren children)
  else if kind == `Lean.Linter.«command_Register_linter_set_:=_» then
    .node (.raw kind) (regroupRegisterLinterSetChildren children)
  else if kind == `commandUnsuppress_compilationIn_ then
    .node (.raw kind) (regroupCommandInWrapperChildren children)
  else if kind == `Lean.Parser.Term.binderTactic then
    .node (.infixChain kind) (regroupBinderTacticChildren children)
  else if isIndexedInfixRawNode kind children then
    .node (.indexedInfix kind) children
  else if isBinaryInfixRawNode kind children then
    match children[0]?, children[1]?, children[2]? with
    | some left, some operator, some right =>
        let parts := appendInfixParts infixPrecedences kind #[] left
        let parts := parts.push operator
        let parts := appendInfixParts infixPrecedences kind parts right
        let parts :=
          if kind == `«term_<|_» then
            regroupLowPriorityInfixRhs <| flattenLowPriorityInfixParts parts
          else
            parts
        .node (.infixChain kind) parts
    | _, _, _ =>
        .node (.raw kind) children
  else if kind == `Lean.Parser.Command.classAbbrev then
    .node .definition children
  else if kind == `Lean.Parser.Command.definition
          || kind == `Lean.Parser.Command.abbrev then
    let children := regroupEquationTrailingClauseChildren children
    match regroupDefinitionChildren children with
    | some definitionChildren => .node .definition definitionChildren
    | none => .node (.raw kind) children
  else if declarationValueCommandKind kind then
    regroupDeclarationValueCommand kind children
  else
    match flattenSimpleDeclarationValueChildren? children with
    | some flattened =>
        .node .definition <| regroupFlattenedDefinitionChildren flattened
    | none => regroupOtherRawNode kind children

partial def regroupTreeWithPrecedences (infixPrecedences : InfixPrecedenceMap)
    : Tree → Tree
  | .missing => .missing
  | .leaf token => .leaf token
  | .node (.raw kind) children =>
      let tree :=
        if isDelimitedCollectionKind kind then
          let children :=
            (flattenDelimitedCollectionChildren children).map
              (regroupTreeWithPrecedences infixPrecedences)
          .node (.raw kind) <| flattenDelimitedCollectionChildren children
        else
          regroupRawNode infixPrecedences kind
            (children.map (regroupTreeWithPrecedences infixPrecedences))
      Tree.annotateTacticTree tree
  | .node kind children =>
      .node kind (children.map (regroupTreeWithPrecedences infixPrecedences))

def regroupTree (tree : Tree) : Tree :=
  regroupTreeWithPrecedences {} tree

def regroupTopLevelCommandAnnotations (tree : Tree) : Tree :=
  match tree with
  | .node .annotatedDeclaration _ => tree
  | _ =>
      match splitDeclarationAnnotations? tree with
      | some (annotations, command) =>
          annotatedDeclarationTreeForCommand annotations command
      | none =>
          match splitDirectCommandDocComment? tree with
          | some (annotations, command) =>
              annotatedDeclarationTreeForCommand annotations command
          | none => tree

def regroupTopLevelAnnotations : Tree → Tree
  | .node (.raw `Lean.Parser.Module.module) children =>
      match children[1]? with
      | some (Tree.node (.raw `null) commands) =>
          Tree.node (.raw `Lean.Parser.Module.module)
          <| children.set! 1
          <| Tree.node (.raw `null) (commands.map regroupTopLevelCommandAnnotations)
      | _ => Tree.node (.raw `Lean.Parser.Module.module) children
  | tree => tree

structure LetBodyParserFact where
  letStart : String.Pos.Raw
  bodyCanStartApplicationArgument : Bool
deriving BEq, Repr

def letBodyParserFact? (facts : Array LetBodyParserFact) (start : String.Pos.Raw)
    : Option LetBodyParserFact :=
  facts.find? fun fact => fact.letStart == start

partial def annotateLetExpressions (facts : Array LetBodyParserFact) : Tree → Tree
  | .missing => .missing
  | .leaf token => .leaf token
  | .node kind children =>
      let children := children.map (annotateLetExpressions facts)
      match kind with
      | .raw rawKind =>
          if rawKind == `Lean.Parser.Term.let
              || rawKind == `Lean.Parser.Term.letI
              || rawKind == `Lean.Parser.Term.letrec then
            let bodyCanStartApplicationArgument :=
              match Tree.firstToken? (.node kind children) with
              | some token =>
                  (letBodyParserFact? facts token.span.start
                    |>.map (·.bodyCanStartApplicationArgument)).getD
                    true
              | none => true
            .node (.letExpression rawKind bodyCanStartApplicationArgument) children
          else
            .node kind children
      | _ => .node kind children

def extractTree
    (source : String) (stx : Syntax)
    (letBodyParserFacts : Array LetBodyParserFact := #[])
    (infixPrecedences : InfixPrecedenceMap := {})
    : Tree :=
  regroupTopLevelAnnotations
  <| annotateLetExpressions letBodyParserFacts
  <| regroupTreeWithPrecedences infixPrecedences
  <| removeOverlappingSourceTokens source
  <| extractRawTree source stx

/-! ## Lean module parsing -/

def importEnvironment
    (imports : Array Import) (leakEnv := false)
    (level : OLeanLevel := .private)
    : IO Environment :=
  LeanEnvironment.importEnvironment { imports, level } (leakEnv := leakEnv)

def importLeanEnvironment : IO Environment := do
  importEnvironment #[{ module := `Lean }]

def parserStateCommandKind : SyntaxNodeKind → Bool
  | `Lean.Parser.Command.open
  | `Lean.Parser.Command.namespace
  | `Lean.Parser.Command.syntax
  | `Lean.Parser.Command.macro
  | `Lean.Parser.Command.notation
  | `Lean.Parser.Command.mixfix
  | `Lean.Parser.Command.infix
  | `Lean.Parser.Command.infixl
  | `Lean.Parser.Command.infixr
  | `Lean.Parser.Command.prefix
  | `Lean.Parser.Command.postfix
  | `Mathlib.Notation3.notation3
  | `Mathlib.Tactic.scopedNS => true
  | _ => false

partial def syntaxContainsParserStateCommandKind : Syntax → Bool
  | Syntax.node _ kind children =>
      parserStateCommandKind kind || children.any syntaxContainsParserStateCommandKind
  | _ => false

def commandUpdatesParserState (command : Syntax) : Bool :=
  syntaxContainsParserStateCommandKind command

def parserStateCommandContext (inputContext : Parser.InputContext)
    : Elab.Command.Context :=
  {
    fileName := inputContext.fileName
    fileMap := inputContext.fileMap
    snap? := none
    cancelTk? := none
  }

def parserModuleContext (commandState : Elab.Command.State)
    : Parser.ParserModuleContext :=
  let scope := commandState.scopes.head!
  {
    env := commandState.env
    options := scope.opts
    currNamespace := scope.currNamespace
    openDecls := scope.openDecls
  }

def syntaxSourceText? (source : String) (stx : Syntax) : Option String := do
  let start ← stx.getPos? (canonicalOnly := true)
  let stop ← stx.getTailPos? (canonicalOnly := true)
  if start < stop then
    some <| sourceText source start stop
  else
    none

def bodyCanStartApplicationArgument
    (parserContext : Parser.ParserModuleContext)
    (bodySource : String)
    : Bool :=
  let inputContext := Parser.mkInputContext bodySource "<let-body-argument-probe>"
  let state :=
    (Parser.termParser Parser.argPrec).fn.run inputContext parserContext
      (Parser.getTokenTable parserContext.env)
      (Parser.mkParserState bodySource)
  !state.hasError && 0 < state.pos

def letBodyIndex? (kind : SyntaxNodeKind) : Option Nat :=
  if kind == `Lean.Parser.Term.let || kind == `Lean.Parser.Term.letI then
    some 4
  else if kind == `Lean.Parser.Term.letrec then
    some 3
  else
    none

partial def collectLetBodyParserFacts
    (source : String) (parserContext : Parser.ParserModuleContext)
    (stx : Syntax) (facts : Array LetBodyParserFact := #[])
    : Array LetBodyParserFact :=
  let facts :=
    match stx with
    | .node _ kind children =>
        match letBodyIndex? kind with
        | some bodyIndex =>
            match stx.getPos? (canonicalOnly := true), children[bodyIndex]? with
            | some letStart, some body =>
                match syntaxSourceText? source body with
                | some bodySource =>
                    facts.push
                      {
                        letStart
                        bodyCanStartApplicationArgument :=
                          bodyCanStartApplicationArgument parserContext bodySource
                      }
                | none => facts
            | _, _ => facts
        | none => facts
    | _ => facts
  stx.getArgs.foldl
    (fun facts child =>
      collectLetBodyParserFacts source parserContext child facts)
    facts

def elaborateParserStateCommand
    (inputContext : Parser.InputContext)
    (commandState : Elab.Command.State)
    (command : Syntax)
    : IO Elab.Command.State := do
  let context := parserStateCommandContext inputContext
  let (_, (_, commandState)) ←
    IO.FS.withIsolatedStreams
      (isolateStderr := true) do
        EIO.toIO (fun _ => IO.userError "failed to update parser command state")
          ((Elab.Command.elabCommand command).run context |>.run commandState)
  pure commandState

partial def parseModuleCommandsQuiet
    (inputContext : Parser.InputContext)
    (state : Parser.ModuleParserState) (messages : MessageLog)
    (commandState : Elab.Command.State)
    (updateParserState : Bool)
    (commands : Array Syntax)
    (letBodyParserFacts : Array LetBodyParserFact)
    : IO (Array Syntax × Array LetBodyParserFact × Elab.Command.State) := do
  let parserContext := parserModuleContext commandState
  let (command, state, messages) :=
    Parser.parseCommand inputContext parserContext state messages
  if Parser.isTerminalCommand command then
    if messages.hasUnreported then
      let messageTexts ← messages.toList.mapM fun message => message.toString
      let details := "\n".intercalate messageTexts
      throw
      <| IO.userError
      <|  if details.isEmpty then
            "failed to parse file"
          else
            s!"failed to parse file:\n{details}"
    else
      pure (commands, letBodyParserFacts, commandState)
  else
    do
      let letBodyParserFacts :=
        collectLetBodyParserFacts inputContext.inputString parserContext command
          letBodyParserFacts
      let commandState ←
        if updateParserState && commandUpdatesParserState command then
          elaborateParserStateCommand inputContext commandState command
        else
          pure commandState
      parseModuleCommandsQuiet inputContext state messages commandState
        updateParserState (commands.push command) letBodyParserFacts

structure ParsedModuleSyntax where
  rawSyntax : Syntax
  letBodyParserFacts : Array LetBodyParserFact
  infixPrecedences : InfixPrecedenceMap
deriving Repr

def parseModuleSyntaxWithEnvCoreDetailed
    (env : Environment) (source fileName : String) (updateParserState : Bool)
    : IO ParsedModuleSyntax := do
  let inputContext := Parser.mkInputContext source fileName
  let (header, state, messages) ← Parser.parseHeader inputContext
  let commandState := Elab.Command.mkState env
  let (commands, letBodyParserFacts, commandState) ←
    try
      parseModuleCommandsQuiet inputContext state messages commandState
        updateParserState #[] #[]
    catch parseError =>
      if updateParserState then
        let frontendState ← Elab.IO.processCommands inputContext state commandState
        let commands :=
          frontendState.commands.filter
            fun command =>
              !Parser.isTerminalCommand command
        pure (commands, #[], frontendState.commandState)
      else
        throw parseError
  let rawSyntax :=
    (mkNode `Lean.Parser.Module.module #[header, mkListNode commands]).raw.updateLeading
  let parserContext := parserModuleContext commandState
  let infixPrecedences :=
    (collectParserPrecedenceFacts parserContext.env parserContext.options
      rawSyntax).infixPrecedences
  pure
    {
      rawSyntax := rawSyntax
      letBodyParserFacts := letBodyParserFacts
      infixPrecedences := infixPrecedences
    }

def parseModuleSyntaxWithEnvCore
    (env : Environment) (source fileName : String) (updateParserState : Bool)
    : IO Syntax := do
  pure
    (← parseModuleSyntaxWithEnvCoreDetailed env source fileName
        updateParserState).rawSyntax

def parseModuleSyntaxWithEnv (env : Environment) (source fileName : String) : IO Syntax :=
  parseModuleSyntaxWithEnvCore env source fileName (updateParserState := true)

def parseModuleSyntaxWithoutParserStateUpdates
    (env : Environment) (source fileName : String)
    : IO Syntax :=
  parseModuleSyntaxWithEnvCore env source fileName (updateParserState := false)

def parseModuleSyntax (source fileName : String) : IO Syntax := do
  parseModuleSyntaxWithEnv (← importLeanEnvironment) source fileName

def parseModuleStringWithEnv (env : Environment) (source fileName : String := "<input>")
    : IO Module := do
  let parsed ←
    parseModuleSyntaxWithEnvCoreDetailed env source fileName (updateParserState := true)
  let tree :=
    extractTree source parsed.rawSyntax parsed.letBodyParserFacts parsed.infixPrecedences
  pure { source, rawSyntax := parsed.rawSyntax, tree, tokens := tree.tokens }

def parseModuleString (source fileName : String := "<input>") : IO Module := do
  parseModuleStringWithEnv (← importLeanEnvironment) source fileName

end SyntaxTree
end LeanFmt
