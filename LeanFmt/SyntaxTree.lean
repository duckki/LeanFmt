import Lean

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
  | application
  | infixChain (kind : SyntaxNodeKind)
  | definition
  | annotatedDeclaration
  | signatureParameters
  | matchDiscriminants
  | matchPatterns
  | doForHeader
deriving BEq, Inhabited, Repr

def nodeKindName : NodeKind → String
  | .raw kind => toString kind
  | .application => "LeanFmt.SyntaxTree.NodeKind.application"
  | .infixChain kind => s!"LeanFmt.SyntaxTree.NodeKind.infixChain {kind}"
  | .definition => "LeanFmt.SyntaxTree.NodeKind.definition"
  | .annotatedDeclaration => "LeanFmt.SyntaxTree.NodeKind.annotatedDeclaration"
  | .signatureParameters => "LeanFmt.SyntaxTree.NodeKind.signatureParameters"
  | .matchDiscriminants => "LeanFmt.SyntaxTree.NodeKind.matchDiscriminants"
  | .matchPatterns => "LeanFmt.SyntaxTree.NodeKind.matchPatterns"
  | .doForHeader => "LeanFmt.SyntaxTree.NodeKind.doForHeader"

inductive Tree where
  | missing
  | leaf (token : Token)
  | node (kind : NodeKind) (children : Array Tree)
deriving BEq, Inhabited, Repr

namespace Tree

partial def tokens : Tree → Array Token
  | Tree.missing => #[]
  | Tree.leaf token => #[token]
  | Tree.node _ children =>
      children.foldl (fun acc child => acc ++ child.tokens) #[]

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
  | _ => none

/-! ## Logical regrouping -/

partial def directLeafAtom? : Tree → Bool
  | .leaf token => token.role == .atom
  | .node (.raw `null) children =>
      match children.toList with
      | [child] => directLeafAtom? child
      | _ => false
  | _ => false

def isBinaryInfixRawNode (kind : SyntaxNodeKind) (children : Array Tree) : Bool :=
  kind != `null
  && kind != `Lean.Parser.Term.app
  && children.size == 3
  && match children[1]? with
      | some operator => directLeafAtom? operator
      | none => false

def appendApplicationArgumentChildren (argumentContainer : Tree) : Array Tree :=
  match argumentContainer with
  | .node (.raw `null) children => children
  | child => #[child]

def appendInfixParts (kind : SyntaxNodeKind) (parts : Array Tree) (tree : Tree)
    : Array Tree :=
  match tree with
  | .node (.infixChain childKind) children =>
      if childKind == kind then
        parts ++ children
      else
        parts.push tree
  | _ => parts.push tree

def regroupSignatureParameters : Tree → Tree
  | .node (.raw `null) children => .node .signatureParameters children
  | tree => tree

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

def regroupDefinitionChildren (children : Array Tree) : Option (Array Tree) := do
  let declVal ← children[3]?
  match declVal with
  | .node (.raw `Lean.Parser.Command.declValSimple) valueChildren =>
      some
      <| childrenRange children 0 3
          ++ valueChildren
          ++ childrenRange children 4 children.size
  | _ => none

def regroupDeclarationChildren (children : Array Tree) : Option (Array Tree) := do
  let modifiers ← children[0]?
  let declaration ← children[1]?
  if (Tree.firstToken? modifiers).isSome then
    some
    <| #[.node .annotatedDeclaration #[modifiers, declaration]]
        ++ childrenRange children 2 children.size
  else
    none

def regroupRawNode (kind : SyntaxNodeKind) (children : Array Tree) : Tree :=
  if kind == `Lean.Parser.Term.app && children.size == 2 then
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
  else if kind == `Lean.Parser.Term.pipeProj && 3 < children.size then
    match children[0]?, children[1]?, children[2]? with
    | some receiver, some operator, some head =>
        .node (.raw kind)
          #[
            receiver,
            operator,
            .node .application
              (#[head] ++ appendApplicationArgumentContainers children 3)
          ]
    | _, _, _ => .node (.raw kind) children
  else if isBinaryInfixRawNode kind children then
    match children[0]?, children[1]?, children[2]? with
    | some left, some operator, some right =>
        let parts := appendInfixParts kind #[] left
        let parts := parts.push operator
        let parts := appendInfixParts kind parts right
        .node (.infixChain kind) parts
    | _, _, _ =>
        .node (.raw kind) children
  else if kind == `Lean.Parser.Command.definition
          || kind == `Lean.Parser.Command.abbrev then
    match regroupDefinitionChildren children with
    | some definitionChildren => .node .definition definitionChildren
    | none => .node (.raw kind) children
  else if kind == `Lean.Parser.Command.declaration then
    match regroupDeclarationChildren children with
    | some declarationChildren => .node (.raw kind) declarationChildren
    | none => .node (.raw kind) children
  else if kind == `Lean.Parser.Command.optDeclSig
          || kind == `Lean.Parser.Command.declSig then
    match children[0]?, children[1]? with
    | some parameters, some typeSpec =>
        .node (.raw kind) #[regroupSignatureParameters parameters, typeSpec]
    | _, _ =>
        .node (.raw kind) children
  else if kind == `Lean.Parser.Term.basicFun then
    match children[0]? with
    | some parameters =>
        .node (.raw kind) <| children.set! 0 (regroupSignatureParameters parameters)
    | none => .node (.raw kind) children
  else if kind == `Lean.Parser.Term.letEqnsDecl then
    match regroupLetEquationSignature children with
    | some children => .node (.raw kind) children
    | none => .node (.raw kind) children
  else if kind == `Lean.Parser.Term.letIdDecl then
    match children[1]? with
    | some parameters =>
        .node (.raw kind) <| children.set! 1 (regroupSignatureParameters parameters)
    | none => .node (.raw kind) children
  else if kind == `Lean.Parser.Term.matchAlt then
    match children[1]? with
    | some patterns =>
        .node (.raw kind) <| children.set! 1 (regroupMatchPatterns patterns)
    | none => .node (.raw kind) children
  else if kind == `Lean.Parser.Term.structInstField then
    match children[0]?, children[1]? >>= structInstFieldParts? with
    | some lvalue, some fieldParts =>
        .node (.raw kind) <| #[lvalue] ++ fieldParts
    | _, _ => .node (.raw kind) children
  else if kind == `Lean.Parser.Term.match then
    match children.findIdx?
            fun child =>
              (Tree.firstToken? child).map (fun token => token.lexeme)
              == some "with" with
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
  else
    .node (.raw kind) children

partial def regroupTree : Tree → Tree
  | .missing => .missing
  | .leaf token => .leaf token
  | .node (.raw kind) children => regroupRawNode kind (children.map regroupTree)
  | .node kind children => .node kind (children.map regroupTree)

def extractTree (source : String) (stx : Syntax) : Tree :=
  regroupTree <| removeOverlappingSourceTokens source <| extractRawTree source stx

/-! ## Lean module parsing -/

def importLeanEnvironment : IO Environment := do
  unsafe enableInitializersExecution
  importModules (loadExts := true) #[{ module := `Lean }] {} 0

partial def parseModuleCommandsQuiet
    (env : Environment) (inputContext : Parser.InputContext)
    (state : Parser.ModuleParserState) (messages : MessageLog)
    (commands : Array Syntax)
    : IO (Array Syntax) := do
  let (command, state, messages) :=
    Parser.parseCommand inputContext { env, options := {} } state messages
  if Parser.isTerminalCommand command then
    if messages.hasUnreported then
      throw <| IO.userError "failed to parse file"
    else
      pure commands
  else
    parseModuleCommandsQuiet env inputContext state messages (commands.push command)

def parseModuleSyntaxWithEnv (env : Environment) (source fileName : String)
    : IO Syntax := do
  let inputContext := Parser.mkInputContext source fileName
  let (header, state, messages) ← Parser.parseHeader inputContext
  let commands ← parseModuleCommandsQuiet env inputContext state messages #[]
  pure
  <| (mkNode `Lean.Parser.Module.module
        #[header, mkListNode commands]).raw.updateLeading

def parseModuleSyntax (source fileName : String) : IO Syntax := do
  parseModuleSyntaxWithEnv (← importLeanEnvironment) source fileName

def parseModuleStringWithEnv (env : Environment) (source fileName : String := "<input>")
    : IO Module := do
  let rawSyntax ← parseModuleSyntaxWithEnv env source fileName
  let tree := extractTree source rawSyntax
  pure { source, rawSyntax, tree, tokens := tree.tokens }

def parseModuleString (source fileName : String := "<input>") : IO Module := do
  parseModuleStringWithEnv (← importLeanEnvironment) source fileName

end SyntaxTree
end LeanFmt
