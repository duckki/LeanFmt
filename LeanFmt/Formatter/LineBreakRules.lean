import LeanFmt.Formatter.SpaceRules

namespace LeanFmt
namespace Formatter
namespace LineBreakRules

open Lean

-----------------------------------------------------------------------------------------
-- Rule interface
-----------------------------------------------------------------------------------------

structure Segment where
  parent : SyntaxTree.Tree
  start : Nat
  stop : Nat
deriving Repr

structure Frame where
  segment : Segment
  childIndex : Nat
deriving Repr

structure RuleContext where
  ancestors : List Frame := []
deriving Repr

structure BreakPoint where
  index : Nat
  indentLevels : Nat := 0
deriving BEq, Repr

inductive StartAlignment where
  | none
  | preferred
  | required
deriving BEq, Repr

-----------------------------------------------------------------------------------------
-- RuleContext utilities
-----------------------------------------------------------------------------------------

namespace Segment

def children? (segment : Segment) : Option (Array SyntaxTree.Tree) :=
  match segment.parent with
  | .node _ children => some children
  | _ => none

def child? (segment : Segment) (index : Nat) : Option SyntaxTree.Tree :=
  if index < segment.start || segment.stop <= index then
    none
  else
    segment.children? >>= fun children => children[index]?

def parentChild? (segment : Segment) (index : Nat) : Option SyntaxTree.Tree :=
  segment.children? >>= fun children => children[index]?

def size (segment : Segment) : Nat :=
  segment.stop - segment.start

def indexes (segment : Segment) : List Nat :=
  List.range' segment.start segment.size

def parentIndexes (segment : Segment) : List Nat :=
  match segment.children? with
  | some children => List.range children.size
  | none => []

def singleChild? (segment : Segment) : Option (Nat × SyntaxTree.Tree) :=
  if segment.stop == segment.start + 1 then
    segment.child? segment.start |>.map fun child => (segment.start, child)
  else
    none

def slice (segment : Segment) (start stop : Nat) : Segment :=
  { parent := segment.parent, start, stop }

def ofTree : SyntaxTree.Tree → Segment
  | tree@(.node _ children) =>
      { parent := tree, start := 0, stop := children.size }
  | tree =>
      { parent := tree, start := 0, stop := 0 }

end Segment

def Segment.rawKind? (segment : Segment) : Option Lean.SyntaxNodeKind :=
  match segment.parent with
  | .node (.raw kind) _ => some kind
  | .node (.tactic kind _ _ _) _ => some kind
  | .node (.letExpression kind _) _ => some kind
  | _ => none

def RuleContext.push (context : RuleContext) (segment : Segment) (childIndex : Nat)
    : RuleContext :=
  { ancestors := { segment, childIndex } :: context.ancestors }

def RuleContext.parentRawKind? (context : RuleContext) : Option Lean.SyntaxNodeKind :=
  match context.ancestors.head? with
  | some frame =>
      match frame.segment.parent with
      | .node (.raw kind) _ => some kind
      | .node (.tactic kind _ _ _) _ => some kind
      | _ => none
  | none => none

def Frame.rawKind? (frame : Frame) : Option Lean.SyntaxNodeKind :=
  match frame.segment.parent with
  | .node (.raw kind) _ => some kind
  | .node (.tactic kind _ _ _) _ => some kind
  | .node (.letExpression kind _) _ => some kind
  | _ => none

def Frame.nodeKind? (frame : Frame) : Option SyntaxTree.NodeKind :=
  match frame.segment.parent with
  | .node kind _ => some kind
  | _ => none

def RuleContext.parentIsSingletonArrayItemWrapper (context : RuleContext) : Bool :=
  match context.ancestors with
  | parent :: grandparent :: _ =>
      parent.rawKind? == some `null
      && parent.segment.size == 1
      && (grandparent.rawKind? == some `«term[_]»
          || grandparent.rawKind? == some `«term#[_,]»)
      && grandparent.childIndex == 1
  | _ => false

def RuleContext.parentIsCommandBinderList (context : RuleContext) : Bool :=
  match context.ancestors with
  | parent :: _ =>
      (parent.rawKind? == some `Lean.Parser.Command.variable
        || parent.rawKind? == some `Lean.Parser.Command.omit
        || parent.rawKind? == some `Lean.Parser.Command.include)
      && parent.childIndex == 1
  | _ => false

def RuleContext.parentIsStructureFieldDefaultValue (context : RuleContext) : Bool :=
  match context.ancestors with
  | parent :: _ =>
      parent.rawKind? == some `Lean.Parser.Command.structSimpleBinder
      && parent.childIndex == 3
  | _ => false

def RuleContext.parentWrapsStructureFieldDefaultValue (context : RuleContext) : Bool :=
  match context.ancestors with
  | parent :: grandparent :: _ =>
      parent.rawKind? == some `null
      && grandparent.rawKind? == some `Lean.Parser.Command.structSimpleBinder
      && grandparent.childIndex == 3
  | _ => false

def RuleContext.parentIsAnnotatedDeclaration (context : RuleContext) : Bool :=
  match context.ancestors with
  | parent :: _ => parent.nodeKind? == some .annotatedDeclaration
  | _ => false

def defaultInheritBase (context : RuleContext) (segment : Segment) : Bool :=
  context.parentIsAnnotatedDeclaration
  || context.parentIsSingletonArrayItemWrapper
  || segment.rawKind? == some `Lean.Parser.Term.letDecl
  || (segment.rawKind? == some `null && context.parentIsCommandBinderList)
  || (segment.rawKind? == some `null && context.parentIsStructureFieldDefaultValue)
  || (segment.rawKind? == some `Lean.Parser.Term.binderDefault
      && context.parentWrapsStructureFieldDefaultValue)
  || (segment.rawKind? == some `null
      && context.parentRawKind? == some `Lean.Parser.Term.doReturn)

def parentIsSignatureParameters (context : RuleContext) : Bool :=
  match context.ancestors with
  | parent :: _ => parent.nodeKind? == some .signatureParameters
  | _ => false

def parentIsRawKind (context : RuleContext) (kind : Lean.SyntaxNodeKind) : Bool :=
  context.parentRawKind? == some kind

def parentIsInfixChain (context : RuleContext) : Bool :=
  match context.ancestors with
  | parent :: _ =>
      match parent.nodeKind? with
      | some (.infixChain _) => true
      | _ => false
  | _ => false

def grandparentIsRawKind (context : RuleContext) (kind : Lean.SyntaxNodeKind) : Bool :=
  match context.ancestors with
  | _ :: grandparent :: _ => grandparent.rawKind? == some kind
  | _ => false

def hasRawKindAncestor (context : RuleContext) (kind : Lean.SyntaxNodeKind) : Bool :=
  context.ancestors.any fun frame => frame.rawKind? == some kind

structure LineBreakRule where
  name : String
  atomic : Bool := false
  formatOriginalChildLeadingBoundary : RuleContext → Segment → Nat → Bool :=
    fun _ _ _ => false
  keepPrefixWithChildFirstLine : RuleContext → Segment → Nat → Bool := fun _ _ _ => false
  useExistingBreaks : RuleContext → Segment → Bool := fun _ _ => false
  mandatory : RuleContext → Segment → Bool := fun _ _ => false
  flow : RuleContext → Segment → Bool := fun _ _ => false
  inheritBase : RuleContext → Segment → Bool := defaultInheritBase
  liftsTailIndentation : RuleContext → Segment → Bool := fun _ _ => false
  startAlignment : RuleContext → Segment → StartAlignment := fun _ _ => .none
  roundUpBaseIndentation : Bool := false
  breakPoints : RuleContext → Segment → List BreakPoint := fun _ _ => []

def boundaryBreak? (segment : Segment) (index indentLevels : Nat) : Option BreakPoint :=
  if segment.start < index && index < segment.stop then
    some { index, indentLevels }
  else
    none

def leadingBreak? (segment : Segment) (index indentLevels : Nat) : Option BreakPoint :=
  if segment.start <= index && index < segment.stop then
    some { index, indentLevels }
  else
    none

def childBoundaryBreaks (segment : Segment) (indentLevels : Nat) : List BreakPoint :=
  match segment.children? with
  | none => []
  | some children =>
      (List.range (children.size - 1)).filterMap
        fun offset => boundaryBreak? segment (offset + 1) indentLevels

-----------------------------------------------------------------------------------------
-- Tree/Token utilities
-----------------------------------------------------------------------------------------

def childIsRawKind (segment : Segment) (index : Nat) (kind : Lean.SyntaxNodeKind)
    : Bool :=
  match segment.child? index with
  | some (.node (.raw childKind) _) => childKind == kind
  | some (.node (.tactic childKind _ _ _) _) => childKind == kind
  | _ => false

partial def treeIsRawKindThroughNullWrappers
    (tree : SyntaxTree.Tree) (kind : Lean.SyntaxNodeKind)
    : Bool :=
  match tree with
  | .node (.raw childKind) children =>
      if childKind == kind then
        true
      else if childKind == `null then
        let content := children.filter fun child => child.firstToken?.isSome
        content.size == 1
        && content[0]?.any fun child => treeIsRawKindThroughNullWrappers child kind
      else
        false
  | .node (.tactic childKind _ _ _) _ => childKind == kind
  | _ => false

def childIsRawKindThroughNullWrappers
    (segment : Segment) (index : Nat) (kind : Lean.SyntaxNodeKind)
    : Bool :=
  segment.child? index |>.any fun child => treeIsRawKindThroughNullWrappers child kind

def firstChildRawKind? (segment : Segment) (kind : Lean.SyntaxNodeKind) : Option Nat :=
  segment.indexes.find? fun index => childIsRawKind segment index kind

def treeHasContent : SyntaxTree.Tree → Bool
  | .missing => false
  | .leaf token => !token.lexeme.isEmpty
  | .node _ children => !children.isEmpty

def treeIsRawKind (tree : SyntaxTree.Tree) (kind : Lean.SyntaxNodeKind) : Bool :=
  match tree with
  | .node (.raw treeKind) _ => treeKind == kind
  | .node (.tactic treeKind _ _ _) _ => treeKind == kind
  | _ => false

partial def treeFirstLexeme? : SyntaxTree.Tree → Option String
  | .missing => none
  | .leaf token =>
      if token.lexeme.isEmpty then none else some token.lexeme
  | .node _ children =>
      children.foldl
        (fun found child =>
          match found with
          | some lexeme => some lexeme
          | none => treeFirstLexeme? child)
        none

def lexemeIn (lexeme : String) (values : List String) : Bool :=
  values.any fun candidate => candidate == lexeme

partial def treeContainsLexeme (lexeme : String) : SyntaxTree.Tree → Bool
  | .missing => false
  | .leaf token => token.lexeme == lexeme
  | .node _ children => children.any (treeContainsLexeme lexeme)

def childIsPatternLambdaArgument (segment : Segment) (index : Nat) : Bool :=
  segment.child? index |>.any SyntaxTree.isPatternLambdaArgument

partial def treeContainsRawKind (kind : Lean.SyntaxNodeKind) : SyntaxTree.Tree → Bool
  | .missing
  | .leaf _ => false
  | .node (.raw treeKind) children =>
      treeKind == kind || children.any (treeContainsRawKind kind)
  | .node (.tactic treeKind _ _ _) children =>
      treeKind == kind || children.any (treeContainsRawKind kind)
  | .node _ children => children.any (treeContainsRawKind kind)

def childContainsNodeKind (segment : Segment) (index : Nat) (kind : SyntaxTree.NodeKind)
    : Bool :=
  segment.child? index |>.any fun child => child.containsNodeKind kind

def childStartsWithLexeme (segment : Segment) (index : Nat) (lexeme : String) : Bool :=
  match segment.child? index with
  | some child => treeFirstLexeme? child == some lexeme
  | none => false

def childIsAtomLexeme (segment : Segment) (index : Nat) (lexeme : String) : Bool :=
  match segment.child? index with
  | some (.leaf token) => token.role == .atom && token.lexeme == lexeme
  | _ => false

def childAtomLexemeEndsWith (segment : Segment) (index : Nat) (suffix : String) : Bool :=
  match segment.child? index with
  | some (.leaf token) => token.role == .atom && token.lexeme.endsWith suffix
  | _ => false

def childIsTrailingSeparator (segment : Segment) (index : Nat) : Bool :=
  match segment.child? index >>= SyntaxTree.Tree.singleToken? with
  | some token => SpaceRules.isTrailingSeparatorToken token.lexeme
  | none => false

def isDoLetFallbackKind (kind : Lean.SyntaxNodeKind) : Bool :=
  kind == `Lean.Parser.Term.doIdDecl
  || kind == `Lean.Parser.Term.doPatDecl
  || kind == `Lean.Parser.Term.doLetArrow
  || kind == `Lean.Parser.Term.doLet
  || kind == `Lean.Parser.Term.doLetElse

def frameSelectsDoLetFallback (frame : Frame) : Bool :=
  frame.rawKind?.any isDoLetFallbackKind
  && (List.range frame.childIndex).any
      fun index =>
        childStartsWithLexeme frame.segment index "|"

def inDoLetFallback (context : RuleContext) : Bool :=
  context.ancestors.head?.any frameSelectsDoLetFallback

def wrappedByDoLetFallbackSequence (context : RuleContext) : Bool :=
  match context.ancestors with
  | parent :: grandparent :: _ =>
      parent.rawKind? == some `Lean.Parser.Term.doSeqIndent
      && frameSelectsDoLetFallback grandparent
  | _ => false

def previousContentIndex? (segment : Segment) (index : Nat) : Option Nat :=
  segment.indexes.foldl
    (fun found candidate =>
      if candidate < index then
        match segment.child? candidate with
        | some child => if treeHasContent child then some candidate else found
        | none => found
      else
        found)
    none

def nonemptyChildIndexes (segment : Segment) : List Nat :=
  segment.indexes.filter
    fun index =>
      match segment.child? index with
      | some child => treeHasContent child
      | none => false

def tokenChildIndexes (segment : Segment) : List Nat :=
  segment.indexes.filter
    fun index =>
      match segment.child? index with
      | some child => child.firstToken?.isSome
      | none => false

inductive CommandKind where
  | moduleKeyword
  | publicImport
  | ordinaryImport
  | moduleDoc
  | declaration
  | other
deriving BEq, Repr

def commandKind (tree : SyntaxTree.Tree) : CommandKind :=
  if treeIsRawKind tree `Lean.Parser.Module.moduleTk then
    .moduleKeyword
  else if treeIsRawKind tree `Lean.Parser.Module.import then
    if treeFirstLexeme? tree == some "public" then .publicImport else .ordinaryImport
  else if treeIsRawKind tree `Lean.Parser.Command.moduleDoc then
    .moduleDoc
  else if treeIsRawKind tree `Lean.Parser.Command.declaration then
    .declaration
  else
    .other

inductive CommandSequenceKind where
  | module
  | header
  | imports
  | commands
deriving BEq, Repr

def inMutualCommandSequence (context : RuleContext) : Bool :=
  context.ancestors.head?.any
    fun parent =>
      parent.rawKind? == some `Lean.Parser.Command.mutual && parent.childIndex == 1

def commandSequenceKind? (context : RuleContext) (segment : Segment)
    : Option CommandSequenceKind :=
  if segment.rawKind? == some `Lean.Parser.Module.module then
    some .module
  else if segment.rawKind? == some `Lean.Parser.Module.header then
    some .header
  else if segment.rawKind? == some `null
          && parentIsRawKind context `Lean.Parser.Module.header then
    some .imports
  else if segment.rawKind? == some `null
          && parentIsRawKind context `Lean.Parser.Module.module then
    some .commands
  else if segment.rawKind? == some `null && inMutualCommandSequence context then
    some .commands
  else
    none

def breakBeforeLexeme? (segment : Segment) (lexeme : String) (indentLevels : Nat)
    : Option BreakPoint := do
  let index ←
    segment.indexes.find? fun index => childStartsWithLexeme segment index lexeme
  boundaryBreak? segment index indentLevels

def contentIndexAfterLexeme? (segment : Segment) (lexeme : String) : Option Nat := do
  let tokenIndex ←
    segment.indexes.find? fun index => childStartsWithLexeme segment index lexeme
  (nonemptyChildIndexes segment).find? fun index => tokenIndex < index

def breakAfterLexeme? (segment : Segment) (lexeme : String) (indentLevels : Nat)
    : Option BreakPoint := do
  let index ← contentIndexAfterLexeme? segment lexeme
  boundaryBreak? segment index indentLevels

def segmentContentCount (segment : Segment) : Nat :=
  match segment.children? with
  | some children =>
      children.foldl
        (fun count child => if treeHasContent child then count + 1 else count) 0
  | none => 0

-----------------------------------------------------------------------------------------
-- Line suffix computation
-----------------------------------------------------------------------------------------

def suffixKeywordLexeme (lexeme : String) : Bool :=
  lexemeIn lexeme ["by", "do", "from", "where", "with", "deriving", "then", "else"]

def suffixOpeningDelimiterLexeme (lexeme : String) : Bool :=
  SpaceRules.stringEndsWithAny lexeme ["(", "[", "{", "⟨", "⟪"]

def treeStartsWithOpeningDelimiter (tree : SyntaxTree.Tree) : Bool :=
  tree.firstToken?.any fun token => suffixOpeningDelimiterLexeme token.lexeme

def suffixClosingDelimiterLexeme (lexeme : String) : Bool :=
  lexemeIn lexeme [")", "]", "}", "⟩", "⟫"]

def suffixDelimiterLexeme (lexeme : String) : Bool :=
  suffixOpeningDelimiterLexeme lexeme
  || suffixClosingDelimiterLexeme lexeme
  || lexemeIn lexeme [",", ";"]

def suffixOperatorLexeme (lexeme : String) : Bool :=
  lexemeIn lexeme
    [
      ":=",
      "=>",
      ":",
      "|",
      "=",
      "==",
      "!",
      "!=",
      "≠",
      "<",
      "≤",
      "<=",
      ">",
      "≥",
      ">=",
      "->",
      "→",
      "∧",
      "∨",
      "/\\",
      "\\/",
      "++",
      "::",
      "+",
      "-",
      "*",
      "/",
      "%"
    ]

def suffixEligibleToken (token : SyntaxTree.Token) : Bool :=
  suffixKeywordLexeme token.lexeme
  || suffixDelimiterLexeme token.lexeme
  || suffixOperatorLexeme token.lexeme

inductive SuffixTokenAction where
  | skip
  | emit
  | stop
deriving BEq, Repr

def frameWrapsOnlySelectedChild (frame : Frame) : Bool :=
  frame.segment.parentIndexes.all
    fun index =>
      index == frame.childIndex
      || match frame.segment.parentChild? index >>= SyntaxTree.Tree.firstToken? with
          | some _ => false
          | none => true

def suffixProjectionMemberIn : List Frame → Bool
  | [] => false
  | parent :: ancestors =>
      if parent.nodeKind? == some (.infixChain `Lean.Parser.Term.proj) then
        parent.childIndex != 0
      else
        frameWrapsOnlySelectedChild parent && suffixProjectionMemberIn ancestors

def suffixProjectionMember (context : RuleContext) : Bool :=
  suffixProjectionMemberIn context.ancestors

def suffixInfixOperatorIn : List Frame → Bool
  | [] => false
  | parent :: ancestors =>
      match parent.nodeKind? with
      | some (.infixChain _) => parent.childIndex % 2 == 1
      | some .lowPriorityInfixRhs => parent.childIndex == 0
      | _ => frameWrapsOnlySelectedChild parent && suffixInfixOperatorIn ancestors

def suffixInfixOperator (context : RuleContext) : Bool :=
  suffixInfixOperatorIn context.ancestors

def suffixTokenAction (context : RuleContext) (token : SyntaxTree.Token)
    : SuffixTokenAction :=
  if token.lexeme.isEmpty then
    .skip
  else if suffixProjectionMember context || suffixInfixOperator context then
    .emit
  else if suffixEligibleToken token then
    .emit
  else
    .stop

def childStartsWithSuffixKeywordToken (segment : Segment) (index : Nat) : Bool :=
  match segment.child? index >>= SyntaxTree.Tree.firstToken? with
  | some token => suffixKeywordLexeme token.lexeme
  | none => false

-----------------------------------------------------------------------------------------
-- Default Rule
-----------------------------------------------------------------------------------------

def defaultChildPresent : SyntaxTree.Tree → Bool
  | .missing => false
  | .leaf token => !token.lexeme.isEmpty
  | .node _ children => !children.isEmpty

def defaultChildIsNonemptyLeaf : SyntaxTree.Tree → Bool
  | .leaf token => !token.lexeme.isEmpty
  | _ => false

def defaultPresentChildIndexBefore? (segment : Segment) (index : Nat) : Option Nat :=
  segment.indexes.foldl
    (fun found candidate =>
      if candidate < index then
        match segment.child? candidate with
        | some child => if defaultChildPresent child then some candidate else found
        | none => found
      else
        found)
    none

def defaultPresentChildIndexAfter? (segment : Segment) (index : Nat) : Option Nat :=
  segment.indexes.find?
    fun candidate =>
      index < candidate
      && match segment.child? candidate with
          | some child => defaultChildPresent child
          | none => false

def defaultChildIsNodeAt (segment : Segment) (index : Nat) : Bool :=
  match segment.child? index with
  | some (.node _ children) => !children.isEmpty
  | _ => false

def defaultInfixBreaks (_context : RuleContext) (segment : Segment) : List BreakPoint :=
  segment.indexes.filterMap
    fun index =>
      match segment.child? index with
      | some child =>
          if defaultChildIsNonemptyLeaf child then
            match defaultPresentChildIndexBefore? segment index,
                  defaultPresentChildIndexAfter? segment index with
            | some beforeIndex, some afterIndex =>
                if defaultChildIsNodeAt segment beforeIndex
                    && defaultChildIsNodeAt segment afterIndex then
                  boundaryBreak? segment index 0
                else
                  none
            | _, _ => none
          else
            none
      | none => none

def defaultPresentChildIndexes (segment : Segment) : List Nat :=
  segment.indexes.filter
    fun index =>
      match segment.child? index with
      | some child => defaultChildPresent child
      | none => false

def defaultChildBreaks (_context : RuleContext) (segment : Segment) : List BreakPoint :=
  match defaultPresentChildIndexes segment with
  | [] => []
  | [_] => []
  | _ :: rest =>
      rest.filterMap fun index => boundaryBreak? segment index 1

def defaultBreaks (context : RuleContext) (segment : Segment) : List BreakPoint :=
  let infixBreaks := defaultInfixBreaks context segment
  if infixBreaks.isEmpty then
    defaultChildBreaks context segment
  else
    infixBreaks

def defaultIsInfix (context : RuleContext) (segment : Segment) : Bool :=
  !(defaultInfixBreaks context segment).isEmpty

def defaultRule : LineBreakRule :=
  {
    name := "default"
    useExistingBreaks := fun context segment => !(defaultBreaks context segment).isEmpty
    flow :=
      fun context segment =>
        !(defaultBreaks context segment).isEmpty && !defaultIsInfix context segment
    liftsTailIndentation := defaultIsInfix
    breakPoints := defaultBreaks
  }

def recursiveSequenceBreaks (_context : RuleContext) (segment : Segment)
    : List BreakPoint :=
  match defaultPresentChildIndexes segment with
  | [] | [_] => []
  | _ :: rest =>
      rest.filterMap fun index => boundaryBreak? segment index 0

def recursiveSequenceRule : LineBreakRule :=
  {
    name := "recursiveSequence"
    useExistingBreaks :=
      fun context segment => !(recursiveSequenceBreaks context segment).isEmpty
    flow := fun context segment => !(recursiveSequenceBreaks context segment).isEmpty
    inheritBase := fun _ _ => true
    breakPoints := recursiveSequenceBreaks
  }

def doIfLetBindRule : LineBreakRule :=
  { defaultRule with name := "doIfLetBind", inheritBase := fun _ _ => true }

-----------------------------------------------------------------------------------------
-- Custom Rules
-----------------------------------------------------------------------------------------

/-! ### Shared wrapper and context rules -/

def singletonDelimitedItemWrapper (context : RuleContext) (segment : Segment) : Bool :=
  context.parentRawKind?.any SyntaxTree.isDelimitedCollectionKind
  && segmentContentCount segment == 1

def rawKindIsQuantifier (kind : Lean.SyntaxNodeKind) : Bool :=
  kind == `Lean.Parser.Term.forall
  || kind == `Lean.Parser.Term.exists
  || kind == `Lean.«term∀__,_»
  || kind == `Lean.«term∃__,_»
  || kind == `«term∃_,_»

def binderOperatorLexeme (lexeme : String) : Bool :=
  ["∀", "∃", "⨆", "⨅", "⋃", "⋂", "∑", "∏", "𝔼", "∫", "∮"].any
    fun operatorPrefix => lexeme.startsWith operatorPrefix

def treeHasBinderBodySeparator (tree : SyntaxTree.Tree) : Bool :=
  let segment := Segment.ofTree tree
  match (nonemptyChildIndexes segment).getLast? with
  | some bodyIndex =>
      segment.indexes.any
        fun index => index < bodyIndex && childStartsWithLexeme segment index ","
  | none => false

def treeHasDirectBinderCollection : SyntaxTree.Tree → Bool
  | .node _ children =>
      children.any
        fun child =>
          treeIsRawKind child `Lean.explicitBinders
          || treeIsRawKind child `Lean.unbracketedExplicitBinders
          || treeIsRawKind child `Batteries.ExtendedBinder.extBinderCollection
  | _ => false

def treeIsBinderOperatorTerm (tree : SyntaxTree.Tree) : Bool :=
  match tree with
  | .node (.raw kind) _ =>
      rawKindIsQuantifier kind
      || ((treeHasDirectBinderCollection tree
            || (treeFirstLexeme? tree).any binderOperatorLexeme)
          && treeHasBinderBodySeparator tree)
  | _ => false

def quantifierBinderSequence (context : RuleContext) : Bool :=
  match context.ancestors with
  | parent :: rest =>
      let direct :=
        match parent.rawKind? with
        | some kind => rawKindIsQuantifier kind && parent.childIndex == 1
        | none => false
      let wrapped :=
        match rest with
        | quantifier :: _ =>
            parent.rawKind? == some `Lean.explicitBinders
            && parent.childIndex == 0
            && (quantifier.rawKind?.map rawKindIsQuantifier).getD false
            && quantifier.childIndex == 1
        | _ => false
      direct || wrapped
  | _ => false

def groupedBinderIdentifierSequence (context : RuleContext) : Bool :=
  match context.ancestors with
  | parent :: _ =>
      (parent.rawKind? == some `Lean.Parser.Term.explicitBinder
        || parent.rawKind? == some `Lean.Parser.Term.implicitBinder)
      && parent.childIndex == 1
  | _ => false

def quantifierIdentifierSequence (context : RuleContext) : Bool :=
  match context.ancestors with
  | unbracketedBinders :: explicitBinders :: quantifier :: _ =>
      unbracketedBinders.rawKind? == some `Lean.unbracketedExplicitBinders
      && unbracketedBinders.childIndex == 0
      && explicitBinders.rawKind? == some `Lean.explicitBinders
      && explicitBinders.childIndex == 0
      && (quantifier.rawKind?.map rawKindIsQuantifier).getD false
      && quantifier.childIndex == 1
  | _ => false

def binderIdentifierSequence (context : RuleContext) : Bool :=
  groupedBinderIdentifierSequence context || quantifierIdentifierSequence context

def commandBinderSequence (context : RuleContext) : Bool :=
  context.parentIsCommandBinderList

def exportIdentifierList (context : RuleContext) : Bool :=
  match context.ancestors with
  | parent :: _ =>
      parent.rawKind? == some `Lean.Parser.Command.export && parent.childIndex == 3
  | _ => false

def openIdentifierList (context : RuleContext) : Bool :=
  match context.ancestors with
  | parent :: _ =>
      parent.rawKind? == some `Lean.Parser.Command.openSimple && parent.childIndex == 0
  | _ => false

def commandAttributeIdentifierList (context : RuleContext) : Bool :=
  match context.ancestors with
  | parent :: _ =>
      parent.rawKind? == some `Lean.Parser.Command.attribute && parent.childIndex == 4
  | _ => false

def allowUnusedTacticIdentifierList (context : RuleContext) : Bool :=
  match context.ancestors with
  | parent :: _ =>
      parent.rawKind?
        == some `Mathlib.Linter.UnusedTactic.«command#allow_unused_tactic!___»
      && parent.childIndex == 4
  | _ => false

def assertNotExistsIdentifierList (context : RuleContext) : Bool :=
  match context.ancestors with
  | parent :: _ =>
      parent.rawKind? == some `Lean.Parser.Command.assertNotExists
      && parent.childIndex == 1
  | _ => false

def parentIsBinderDefaultWrapper (context : RuleContext) : Bool :=
  match context.ancestors with
  | parent :: _ =>
      (parent.rawKind? == some `Lean.Parser.Term.explicitBinder
        || parent.rawKind? == some `Lean.Parser.Term.implicitBinder)
      && parent.childIndex == 3
  | _ => false

def nullInheritBase (context : RuleContext) (segment : Segment) : Bool :=
  defaultInheritBase context segment
  || singletonDelimitedItemWrapper context segment
  || (segment.singleChild?.any
        fun (_, child) =>
          treeIsRawKind child `Lean.Elab.ConfigEval.configEntries)
  || parentIsBinderDefaultWrapper context
  || quantifierBinderSequence context
  || parentIsRawKind context `Lean.Parser.Command.extends
  || parentIsRawKind context `Lean.Parser.Term.structInstFields
  || parentIsRawKind context `Lean.Parser.Term.letRecDecls
  || parentIsRawKind context `Lean.Parser.Term.letRecDecl
  || parentIsRawKind context `Lean.Parser.Tactic.cases
  || parentIsRawKind context `Lean.Parser.Tactic.inductionAlts
  || parentIsRawKind context `Lean.Parser.Tactic.inductionAlt
  || parentIsRawKind context `BigOperators.bigOpBinder
  || parentIsRawKind context `Batteries.ExtendedBinder.extBinder
  || parentIsRawKind context `Batteries.ExtendedBinder.extBinderCollection
  || commandAttributeIdentifierList context
  || allowUnusedTacticIdentifierList context
  || assertNotExistsIdentifierList context
  || wrappedByDoLetFallbackSequence context

def attachedBodyStart (segment : Segment) (index : Nat) : Bool :=
  childStartsWithLexeme segment index "do" || childStartsWithLexeme segment index "by"

def attachedBodyFollowsDelimiter (context : RuleContext) (delimiter : String) : Bool :=
  match context.ancestors with
  | parent :: _ =>
      let segment := Segment.ofTree parent.segment.parent
      match previousContentIndex? segment parent.childIndex with
      | some index => childStartsWithLexeme segment index delimiter
      | none => false
  | _ => false

partial def treeContainsDoLetFallback : SyntaxTree.Tree → Bool
  | .missing
  | .leaf _ => false
  | tree@(.node (.raw kind) children) =>
      (isDoLetFallbackKind kind && treeContainsLexeme "|" tree)
      || children.any treeContainsDoLetFallback
  | .node _ children => children.any treeContainsDoLetFallback

def nestedInDoSequence (context : RuleContext) : Bool :=
  context.ancestors.any fun frame => frame.rawKind? == some `Lean.Parser.Term.doSeqIndent

def canRetainOriginalLayoutForOverflow (context : RuleContext) : SyntaxTree.Tree → Bool
  | tree@(.node (.raw `Lean.Parser.Term.doSeqIndent) _) =>
      !nestedInDoSequence context
      && !inDoLetFallback context
      && !wrappedByDoLetFallbackSequence context
      && !treeContainsDoLetFallback tree
  | _ => false

def canRetainParentRelativeOriginalLayoutForOverflow (context : RuleContext)
    : SyntaxTree.Tree → Bool
  | .node (.raw `Lean.Parser.Term.doSeqIndent) _ => !nestedInDoSequence context
  | _ => false

def infixAttachedBodyAssignmentValue (context : RuleContext) (segment : Segment) : Bool :=
  match context.ancestors, (nonemptyChildIndexes segment).head? with
  | parent :: _, some firstIndex =>
      attachedBodyStart segment firstIndex
      && contentIndexAfterLexeme? parent.segment ":=" == some parent.childIndex
  | _, _ => false

def delimiterValueBreak? (segment : Segment) (delimiter : String)
    : Option BreakPoint := do
  let valueIndex ← contentIndexAfterLexeme? segment delimiter
  if attachedBodyStart segment valueIndex then
    none
  else
    boundaryBreak? segment valueIndex 1

def declarationValueBreak? (segment : Segment) : Option BreakPoint :=
  delimiterValueBreak? segment ":="

def declarationValueBreaks (_context : RuleContext) (segment : Segment)
    : List BreakPoint :=
  [declarationValueBreak? segment].filterMap id
  ++ segment.indexes.filterMap
      fun index =>
        if segment.start < index
            && (childIsRawKindThroughNullWrappers
                  segment index `Lean.Parser.Term.whereDecls
                || (childIsRawKind segment index `Lean.Parser.Termination.suffix
                    && (segment.child? index).any treeHasContent)) then
          boundaryBreak? segment index 0
        else
          none

def lowPriorityInfixSegment (segment : Segment) : Bool :=
  match segment.parent with
  | .node (.infixChain `«term_<|_») _ => true
  | _ => false

def lowPriorityInfixRhsSegment (segment : Segment) : Bool :=
  match segment.parent with
  | .node .lowPriorityInfixRhs _ => true
  | _ => false

def childIsLowPriorityInfixRhs (segment : Segment) (index : Nat) : Bool :=
  match segment.child? index with
  | some (.node .lowPriorityInfixRhs _) => true
  | _ => false

def lowPriorityInfixRhsHasMandatoryAlignedBody (segment : Segment) : Bool :=
  if !lowPriorityInfixRhsSegment segment then
    false
  else
    match segment.child? (segment.start + 1) with
    | some (.node (.letExpression _ _) _) => true
    | some (.node (.raw kind) _) =>
        kind == `Lean.Parser.Term.let
        || kind == `Lean.Parser.Term.letrec
        || kind == `Lean.Parser.Term.have
        || kind == `Lean.Parser.Term.haveI
    | _ => false

def lowPriorityInfixRhsHasAttachedBody (segment : Segment) : Bool :=
  lowPriorityInfixRhsSegment segment
  && (attachedBodyStart segment (segment.start + 1)
      || childStartsWithLexeme segment (segment.start + 1) "calc"
      || lowPriorityInfixRhsHasMandatoryAlignedBody segment)

def childLowPriorityInfixRhsHasAttachedBody (segment : Segment) (index : Nat) : Bool :=
  match segment.child? index with
  | some child => lowPriorityInfixRhsHasAttachedBody (Segment.ofTree child)
  | none => false

def lowPriorityInfixRhsCanFlow (segment : Segment) : Bool :=
  lowPriorityInfixRhsSegment segment
  && (attachedBodyStart segment (segment.start + 1)
      || lowPriorityInfixRhsHasMandatoryAlignedBody segment)

def childLowPriorityInfixRhsCanFlow (segment : Segment) (index : Nat) : Bool :=
  match segment.child? index with
  | some child => lowPriorityInfixRhsCanFlow (Segment.ofTree child)
  | none => false

def lowPriorityInfixAllRhsCanFlow (segment : Segment) : Bool :=
  lowPriorityInfixSegment segment
  && segment.indexes.all
      fun index =>
        index == segment.start || childLowPriorityInfixRhsCanFlow segment index

partial def treeContainsAttachedBodyInfix : SyntaxTree.Tree → Bool
  | .missing => false
  | .leaf _ => false
  | tree@(.node _ children) =>
      let segment := Segment.ofTree tree
      lowPriorityInfixRhsHasAttachedBody segment
      || children.any treeContainsAttachedBodyInfix

partial def treeContainsProofTree : SyntaxTree.Tree → Bool
  | .missing => false
  | .leaf _ => false
  | .node (.proofBody _) _ => true
  | .node _ children => children.any treeContainsProofTree

def childHasNestedProofBody (segment : Segment) (index : Nat) : Bool :=
  !attachedBodyStart segment index
  && match segment.child? index with
      | some child => treeContainsProofTree child
      | none => false

def declarationValueHasAttachedBodyInfix (segment : Segment) : Bool :=
  match contentIndexAfterLexeme? segment ":=" with
  | none => false
  | some valueIndex =>
      match segment.child? valueIndex with
      | some value => treeContainsAttachedBodyInfix value
      | none => false

def declarationValueHasNestedProofBody (segment : Segment) : Bool :=
  match contentIndexAfterLexeme? segment ":=" with
  | some valueIndex => childHasNestedProofBody segment valueIndex
  | none => false

/-! ### Declarations, structures, and collections -/

def derivingBreaks (_context : RuleContext) (segment : Segment) : List BreakPoint :=
  match segment.indexes.find?
          fun index => childStartsWithLexeme segment index "deriving" with
  | some index =>
      match boundaryBreak? segment index 0 with
      | some breakPoint => [breakPoint]
      | none => []
  | none => []

def derivingClauseBreaks (_context : RuleContext) (segment : Segment) : List BreakPoint :=
  segment.indexes.filterMap
    fun index =>
      match previousContentIndex? segment index with
      | some previousIndex =>
          if childStartsWithLexeme segment previousIndex "," then
            boundaryBreak? segment index 1
          else
            none
      | none => none

def structureParentBreaks (context : RuleContext) (segment : Segment) : List BreakPoint :=
  if parentIsRawKind context `Lean.Parser.Command.extends then
    segment.indexes.filterMap
      fun index =>
        match previousContentIndex? segment index with
        | some previousIndex =>
            if childStartsWithLexeme segment previousIndex "," then
              boundaryBreak? segment index 1
            else
              none
        | none => none
  else
    []

def terminationSuffixChildBreaksWithIndent (segment : Segment) (indentLevels : Nat)
    : List BreakPoint :=
  segment.indexes.filterMap
    fun index =>
      match segment.child? index with
      | some child =>
          if childIsRawKind segment index `Lean.Parser.Termination.suffix
              && child.firstToken?.isSome then
            boundaryBreak? segment index indentLevels
          else
            none
      | none => none

def terminationSuffixChildBreaks (segment : Segment) : List BreakPoint :=
  terminationSuffixChildBreaksWithIndent segment 0

def declarationTrailingClauseBreaks (segment : Segment) : List BreakPoint :=
  terminationSuffixChildBreaks segment
  ++ segment.indexes.filterMap
      fun index =>
        if 3 < index
            && childIsRawKindThroughNullWrappers
                segment index `Lean.Parser.Term.whereDecls then
          boundaryBreak? segment index 0
        else
          none

def definitionBreaks (context : RuleContext) (segment : Segment) : List BreakPoint :=
  let valueBreak := [declarationValueBreak? segment].filterMap id
  valueBreak ++ declarationTrailingClauseBreaks segment ++ derivingBreaks context segment

def leadingAnnotationBreak? (segment : Segment) : Option BreakPoint := do
  let firstIndex ← (nonemptyChildIndexes segment).head?
  let firstChild ← segment.child? firstIndex
  if !(childStartsWithLexeme segment firstIndex "@["
        || treeContainsLexeme "@[" firstChild
        || SyntaxTree.isDocCommentContainer firstChild) then
    none
  else
    let commandIndex ←
      (nonemptyChildIndexes segment).find? fun index => firstIndex < index
    boundaryBreak? segment commandIndex 0

def leadingAnnotationBreaks (_context : RuleContext) (segment : Segment)
    : List BreakPoint :=
  [leadingAnnotationBreak? segment].filterMap id

def annotatedDeclarationBreaks : RuleContext → Segment → List BreakPoint :=
  leadingAnnotationBreaks

def annotatedDeclarationKeepsModifierPrefix (segment : Segment) (index : Nat) : Bool :=
  match (nonemptyChildIndexes segment).reverse.find?
          fun candidate => candidate < index with
  | some previousIndex =>
      segment.child? previousIndex
      |>.any
          fun child =>
            SyntaxTree.rawKind? child == some `Lean.Parser.Command.declModifiers
            && !treeContainsLexeme "@[" child
            && !SyntaxTree.isDocCommentContainer child
  | none => false

def declarationModifierBreaks (_context : RuleContext) (segment : Segment)
    : List BreakPoint :=
  match defaultPresentChildIndexes segment with
  | [] => []
  | [_] => []
  | _ :: rest =>
      rest.filterMap fun index => boundaryBreak? segment index 0

def structureHeaderBreaks (_context : RuleContext) (segment : Segment)
    : List BreakPoint :=
  [breakBeforeLexeme? segment "extends" 2].filterMap id

def structFieldsBreaks (_context : RuleContext) (segment : Segment) : List BreakPoint :=
  match leadingBreak? segment segment.start 1 with
  | some breakPoint => [breakPoint]
  | none => []

def structureConstructorBreaks (_context : RuleContext) (segment : Segment)
    : List BreakPoint :=
  [leadingBreak? segment segment.start 1].filterMap id

def structureDerivingBreaks (_context : RuleContext) (segment : Segment)
    : List BreakPoint :=
  [leadingBreak? segment segment.start 0].filterMap id

def structureFieldBreaks (context : RuleContext) (segment : Segment) : List BreakPoint :=
  if parentIsRawKind context `Lean.Parser.Command.structFields then
    match nonemptyChildIndexes segment with
    | [] => []
    | _ :: rest =>
        rest.filterMap fun index => boundaryBreak? segment index 0
  else
    []

def structInstFieldIndexes (segment : Segment) : List Nat :=
  segment.indexes.filter
    fun index => childIsRawKind segment index `Lean.Parser.Term.structInstField

def structInstFieldChildCount : SyntaxTree.Tree → Nat
  | .node (.raw `Lean.Parser.Term.structInstField) _ => 1
  | .node (.raw `null) children =>
      children.foldl
        (fun count child =>
          match child with
          | .node (.raw `Lean.Parser.Term.structInstField) _ => count + 1
          | _ => count)
        0
  | _ => 0

def structInstFieldCount (segment : Segment) : Nat :=
  segment.indexes.foldl
    (fun count index =>
      match segment.child? index with
      | some (.node (.raw `Lean.Parser.Term.structInstFields) children) =>
          count
          + children.foldl (fun count child => count + structInstFieldChildCount child) 0
      | _ => count)
    0

def structInstHasWith (segment : Segment) : Bool :=
  match firstChildRawKind? segment `Lean.Parser.Term.structInstFields with
  | some fieldsIndex =>
      segment.indexes.any
        fun index =>
          index < fieldsIndex
          && match segment.child? index with
              | some child => treeContainsLexeme "with" child
              | none => false
  | none => false

def hasCommaBetweenFields (segment : Segment) (left right : Nat) : Bool :=
  segment.indexes.any
    fun index =>
      left < index && index < right && childStartsWithLexeme segment index ","

def hasMissingCommaBetweenFields (segment : Segment) : List Nat → Bool
  | left :: right :: rest =>
      !hasCommaBetweenFields segment left right
      || hasMissingCommaBetweenFields segment (right :: rest)
  | _ => false

def structInstFieldBreaks (context : RuleContext) (segment : Segment) : List BreakPoint :=
  if parentIsRawKind context `Lean.Parser.Term.structInstFields then
    match structInstFieldIndexes segment with
    | [] => []
    | [_] => []
    | _ :: rest =>
        rest.filterMap fun index => boundaryBreak? segment index 0
  else
    []

def structInstFieldBodyBreaks (_context : RuleContext) (segment : Segment)
    : List BreakPoint :=
  let assignmentBreak := [delimiterValueBreak? segment ":="].filterMap id
  let equationBreak :=
    match segment.indexes.find?
            fun index =>
              segment.child? index
              |>.any (treeContainsRawKind `Lean.Parser.Term.structInstFieldEqns) with
    | some equationIndex => [boundaryBreak? segment equationIndex 1].filterMap id
    | none => []
  assignmentBreak ++ equationBreak

def delimitedItemIndexes (segment : Segment) : List Nat :=
  match nonemptyChildIndexes segment with
  | [] | [_] => []
  | _open :: rest =>
      rest.dropLast.filter
        fun index =>
          !childStartsWithLexeme segment index ","
          && !(segment.rawKind? == some `Matrix.matrixNotation
                && childStartsWithLexeme segment index ";")

def delimitedItemCount (segment : Segment) : Nat :=
  (delimitedItemIndexes segment).length

def delimitedCollectionBreaks (segment : Segment) (includeSingleton : Bool := false)
    : List BreakPoint :=
  let itemCount := delimitedItemCount segment
  if 1 < itemCount || (includeSingleton && 0 < itemCount) then
    let itemBreaks :=
      (delimitedItemIndexes segment).filterMap fun index => boundaryBreak? segment index 1
    let closeBreak :=
      match (nonemptyChildIndexes segment).getLast? with
      | some index => [boundaryBreak? segment index 0].filterMap id
      | none => []
    itemBreaks ++ closeBreak
  else
    []

def tupleItemIndexes (segment : Segment) : List Nat :=
  delimitedItemIndexes segment

def tupleItemCount (segment : Segment) : Nat :=
  delimitedItemCount segment

def tupleBreaks (_context : RuleContext) (segment : Segment) : List BreakPoint :=
  delimitedCollectionBreaks segment

def anonymousCtorItemIndexes (segment : Segment) : List Nat :=
  delimitedItemIndexes segment

def anonymousCtorItemCount (segment : Segment) : Nat :=
  delimitedItemCount segment

def anonymousCtorBreaks (_context : RuleContext) (segment : Segment) : List BreakPoint :=
  delimitedCollectionBreaks segment

def setBuilderBreaks (_context : RuleContext) (segment : Segment) : List BreakPoint :=
  [breakAfterLexeme? segment "|" 1, breakBeforeLexeme? segment "}" 0].filterMap id

def arrayItemIndexes (segment : Segment) : List Nat :=
  delimitedItemIndexes segment

def arrayItemCount (segment : Segment) : Nat :=
  delimitedItemCount segment

def arrayBreaks (_context : RuleContext) (segment : Segment) : List BreakPoint :=
  delimitedCollectionBreaks segment (segment.rawKind? == some `«term#[_,]»)

def matrixNotationRule : LineBreakRule :=
  {
    name := "matrixNotation"
    useExistingBreaks := fun _ _ => true
    flow := fun _ _ => true
    inheritBase := fun _ segment => 1 < delimitedItemCount segment
    roundUpBaseIndentation := true
    breakPoints := fun _ segment => delimitedCollectionBreaks segment
  }

def structInstFieldsMandatory (context : RuleContext) (segment : Segment) : Bool :=
  parentIsRawKind context `Lean.Parser.Term.structInstFields
  && hasMissingCommaBetweenFields segment (structInstFieldIndexes segment)

def structInstBreaks (_context : RuleContext) (segment : Segment) : List BreakPoint :=
  if 1 < structInstFieldCount segment || structInstHasWith segment then
    let hasWith := structInstHasWith segment
    let fieldBreak :=
      if hasWith then
        match firstChildRawKind? segment `Lean.Parser.Term.structInstFields with
        | some index =>
            match boundaryBreak? segment index 2 with
            | some breakPoint => [breakPoint]
            | none => []
        | none => []
      else
        []
    match segment.indexes.find? fun index => childStartsWithLexeme segment index "{",
          segment.indexes.find? fun index => childStartsWithLexeme segment index "}" with
    | some openIndex, some closeIndex =>
        let openBreak :=
          match (nonemptyChildIndexes segment).find? fun index => openIndex < index with
          | some index => [boundaryBreak? segment index 1].filterMap id
          | none => []
        let closeBreak := [boundaryBreak? segment closeIndex 0].filterMap id
        openBreak ++ fieldBreak ++ closeBreak
    | _, _ => []
  else
    []

def structureUpdateSourceIndexes (segment : Segment) : List Nat :=
  (nonemptyChildIndexes segment).takeWhile
    (fun index => !childStartsWithLexeme segment index "with")
  |>.filter (fun index => !childStartsWithLexeme segment index ",")

def structInstHasMultipleUpdateSources (segment : Segment) : Bool :=
  segment.indexes.any
    fun index =>
      match segment.child? index with
      | some tree@(.node .structureUpdate _) =>
          1 < (structureUpdateSourceIndexes (Segment.ofTree tree)).length
      | _ => false

def structureUpdateBreaks (_context : RuleContext) (segment : Segment)
    : List BreakPoint :=
  match structureUpdateSourceIndexes segment with
  | [] | [_] => []
  | _ :: rest => rest.filterMap fun index => boundaryBreak? segment index 0

def typeAscriptionBreaks (_context : RuleContext) (segment : Segment) : List BreakPoint :=
  match segment.indexes.find? fun index => childStartsWithLexeme segment index ":" with
  | some index =>
      match boundaryBreak? segment index 1 with
      | some breakPoint => [breakPoint]
      | none => []
  | none => []

def namedArgumentBreaks (_context : RuleContext) (segment : Segment) : List BreakPoint :=
  [boundaryBreak? segment 3 1, boundaryBreak? segment 4 0].filterMap id

/-! ### Declaration lists and module commands -/

def inductiveAlternativeBreaks (context : RuleContext) (segment : Segment)
    : List BreakPoint :=
  if parentIsRawKind context `Lean.Parser.Command.inductive
      || parentIsRawKind context `Lean.Parser.Command.classInductive then
    match segment.indexes.filter
            fun index =>
              childIsRawKind segment index `Lean.Parser.Command.ctor with
    | [] => []
    | _ :: rest =>
        rest.filterMap fun index => boundaryBreak? segment index 0
  else
    []

def tacticAlternativeSequenceBreaks (context : RuleContext) (segment : Segment)
    : List BreakPoint :=
  if parentIsRawKind context `Lean.Parser.Tactic.inductionAlts then
    match segment.indexes.filter
            fun index =>
              childIsRawKind segment index `Lean.Parser.Tactic.inductionAlt with
    | [] | [_] => []
    | _ :: rest => rest.filterMap fun index => boundaryBreak? segment index 0
  else
    []

def tacticSequenceItemBreaks (context : RuleContext) (segment : Segment)
    : List BreakPoint :=
  if parentIsRawKind context `Lean.Parser.Tactic.tacticSeq1Indented
      && context.ancestors.any
          fun frame =>
            frame.nodeKind?.any
              fun
              | .proofBody _ => true
              | _ => false then
    match nonemptyChildIndexes segment with
    | [] | [_] => []
    | _ :: rest => rest.filterMap fun index => boundaryBreak? segment index 0
  else
    []

def tacticAlternativeContainerBreaks (_context : RuleContext) (segment : Segment)
    : List BreakPoint :=
  segment.indexes.filterMap
    fun index =>
      if (segment.child? index).any
          (treeContainsRawKind `Lean.Parser.Tactic.inductionAlt) then
        boundaryBreak? segment index 0
      else
        none

partial def tacticAlternativesStartWithDefault : SyntaxTree.Tree → Bool
  | .node kind children =>
      let isAlternativeContainer :=
        match kind with
        | .raw rawKind | .tactic rawKind _ _ _ =>
            rawKind == `Lean.Parser.Tactic.inductionAlts
        | _ => false
      if isAlternativeContainer then
        match children.find? treeHasContent with
        | some child => !treeContainsRawKind `Lean.Parser.Tactic.inductionAlt child
        | none => false
      else
        children.any tacticAlternativesStartWithDefault
  | _ => false

def alternativeBodyIndentLevels : Nat :=
  2

def tacticLayoutOwnerBreaks (context : RuleContext) (segment : Segment)
    : List BreakPoint :=
  if segment.rawKind? == some `Lean.Parser.Tactic.cases
      || segment.rawKind? == some `Lean.Parser.Tactic.induction then
    match defaultPresentChildIndexes segment with
    | [] | [_] => []
    | _ :: rest =>
        rest.filterMap
          fun index =>
            if (segment.child? index).any
                (treeContainsRawKind `Lean.Parser.Tactic.inductionAlts) then
              let indentLevels :=
                if (segment.child? index).any tacticAlternativesStartWithDefault then
                  alternativeBodyIndentLevels
                else
                  0
              boundaryBreak? segment index indentLevels
            else if childContainsNodeKind segment index .namedDiscriminant then
              none
            else if (segment.child? index).any
                      fun
                      | .node (.proofBody _) _ => true
                      | _ => false then
              boundaryBreak? segment index alternativeBodyIndentLevels
            else
              boundaryBreak? segment index 1
  else
    defaultBreaks context segment

def tacticEliminationHeaderBreaks (_context : RuleContext) (segment : Segment)
    : List BreakPoint :=
  match defaultPresentChildIndexes segment with
  | [] | [_] => []
  | _ :: targetIndex :: rest =>
      let targetIsNamed :=
        match segment.parent with
        | .node (.tacticEliminationHeader targetIsNamed) _ => targetIsNamed
        | _ => false
      let hasIdentifierClause :=
        segment.indexes.any
          fun index =>
            (segment.child? index).any
              fun
              | .node .tacticIdentifierClause _ => true
              | _ => false
      let targetBreak :=
        if targetIsNamed || hasIdentifierClause then
          []
        else
          [boundaryBreak? segment targetIndex 1].filterMap id
      targetBreak
      ++ rest.filterMap
          fun index =>
            match segment.child? index with
            | some (.node .tacticIdentifierClause _) => none
            | some (.node (.proofBody _) _) =>
                boundaryBreak? segment index alternativeBodyIndentLevels
            | _ => boundaryBreak? segment index 1

def tacticAlternativeBodyBreaks (_context : RuleContext) (segment : Segment)
    : List BreakPoint :=
  if segment.rawKind? == some `Lean.Parser.Tactic.inductionAlt then
    segment.indexes.filterMap
      fun index =>
        match segment.child? index with
        | some (.node (.proofBody _) _) =>
            boundaryBreak? segment index alternativeBodyIndentLevels
        | _ => none
  else
    []

def tacticIdentifierClauseBreaks (_context : RuleContext) (segment : Segment)
    : List BreakPoint :=
  match nonemptyChildIndexes segment with
  | [] | [_] => []
  | _ :: rest => rest.filterMap fun index => boundaryBreak? segment index 2

def quantifierBinderBreaks (context : RuleContext) (segment : Segment)
    : List BreakPoint :=
  if quantifierBinderSequence context then
    match nonemptyChildIndexes segment with
    | [] => []
    | [_] => []
    | _ :: rest => rest.filterMap fun index => boundaryBreak? segment index 2
  else
    []

def extendedBinderCollectionBreaks (context : RuleContext) (segment : Segment)
    : List BreakPoint :=
  if parentIsRawKind context `Batteries.ExtendedBinder.extBinderCollection then
    childBoundaryBreaks segment 0
  else
    []

def binderIdentifierBreaks (context : RuleContext) (segment : Segment)
    : List BreakPoint :=
  if binderIdentifierSequence context then
    match nonemptyChildIndexes segment with
    | [] => []
    | [_] => []
    | _ :: rest => rest.filterMap fun index => boundaryBreak? segment index 1
  else
    []

def commandBinderBreaks (context : RuleContext) (segment : Segment) : List BreakPoint :=
  if commandBinderSequence context then
    match nonemptyChildIndexes segment with
    | [] => []
    | [_] => []
    | _ :: rest => rest.filterMap fun index => boundaryBreak? segment index 1
  else
    []

def openIdentifierBreaks (context : RuleContext) (segment : Segment) : List BreakPoint :=
  if openIdentifierList context then
    match nonemptyChildIndexes segment with
    | [] => []
    | [_] => []
    | _ :: rest => rest.filterMap fun index => boundaryBreak? segment index 1
  else
    []

def commandAttributeIdentifierBreaks (context : RuleContext) (segment : Segment)
    : List BreakPoint :=
  if commandAttributeIdentifierList context then
    match nonemptyChildIndexes segment with
    | [] => []
    | first :: rest =>
        [leadingBreak? segment first 1].filterMap id
        ++ rest.filterMap fun index => boundaryBreak? segment index 1
  else
    []

def allowUnusedTacticIdentifierBreaks (context : RuleContext) (segment : Segment)
    : List BreakPoint :=
  if allowUnusedTacticIdentifierList context then
    match nonemptyChildIndexes segment with
    | [] => []
    | first :: rest =>
        [leadingBreak? segment first 0].filterMap id
        ++ rest.filterMap fun index => boundaryBreak? segment index 0
  else
    []

def assertNotExistsIdentifierBreaks (context : RuleContext) (segment : Segment)
    : List BreakPoint :=
  if assertNotExistsIdentifierList context then
    childBoundaryBreaks segment 0
  else
    []

def matchPatternBreaks (_context : RuleContext) (segment : Segment) : List BreakPoint :=
  segment.indexes.filterMap
    fun index =>
      if childStartsWithLexeme segment index "|" then
        boundaryBreak? segment index 0
      else
        match previousContentIndex? segment index with
        | some previousIndex =>
            if childStartsWithLexeme segment previousIndex "," then
              boundaryBreak? segment index 1
            else
              none
        | none => none

def matchDiscriminantBreaks (_context : RuleContext) (segment : Segment)
    : List BreakPoint :=
  segment.indexes.filterMap
    fun index =>
      match previousContentIndex? segment index with
      | some previousIndex =>
          if childStartsWithLexeme segment previousIndex "," then
            boundaryBreak? segment index 0
          else
            none
      | none => none

def matchDiscriminantsFollowMotive (context : RuleContext) : Bool :=
  match context.ancestors with
  | parent :: _ =>
      parent.rawKind? == some `Lean.Parser.Term.match
      && (List.range parent.childIndex).any
          fun index =>
            parent.segment.parentChild? index
            |>.any (treeContainsRawKind `Lean.Parser.Term.motive)
  | _ => false

def exportItemBreaks (context : RuleContext) (segment : Segment) : List BreakPoint :=
  if exportIdentifierList context then
    match nonemptyChildIndexes segment with
    | [] => []
    | [_] => []
    | _ :: rest => rest.filterMap fun index => boundaryBreak? segment index 0
  else
    []

def assertNotExistsBreaks (_context : RuleContext) (segment : Segment)
    : List BreakPoint :=
  [breakAfterLexeme? segment "assert_not_exists" 1].filterMap id

def moduleImportBreaks (context : RuleContext) (segment : Segment) : List BreakPoint :=
  if parentIsRawKind context `Lean.Parser.Module.header then
    match nonemptyChildIndexes segment with
    | [] => []
    | [_] => []
    | _ :: rest =>
        rest.filterMap fun index => boundaryBreak? segment index 0
  else
    []

def moduleHeaderBreaks (_context : RuleContext) (segment : Segment) : List BreakPoint :=
  if segment.rawKind? == some `Lean.Parser.Module.header then
    match tokenChildIndexes segment with
    | [] => []
    | [_] => []
    | _ :: rest =>
        rest.filterMap fun index => boundaryBreak? segment index 0
  else
    []

def moduleBodyBreaks (_context : RuleContext) (segment : Segment) : List BreakPoint :=
  if segment.rawKind? == some `Lean.Parser.Module.module then
    match tokenChildIndexes segment with
    | [] => []
    | [_] => []
    | _ :: rest =>
        rest.filterMap fun index => boundaryBreak? segment index 0
  else
    []

def moduleCommandBreaks (context : RuleContext) (segment : Segment) : List BreakPoint :=
  if parentIsRawKind context `Lean.Parser.Module.module then
    match nonemptyChildIndexes segment with
    | [] => []
    | [_] => []
    | _ :: rest =>
        rest.filterMap fun index => boundaryBreak? segment index 0
  else
    []

def mutualCommandBreaks (context : RuleContext) (segment : Segment) : List BreakPoint :=
  if inMutualCommandSequence context then
    match nonemptyChildIndexes segment with
    | []
    | [_] => []
    | _ :: rest =>
        rest.filterMap fun index => boundaryBreak? segment index 0
  else
    []

def letRecDeclarationSequenceBreaks (context : RuleContext) (segment : Segment)
    : List BreakPoint :=
  if parentIsRawKind context `Lean.Parser.Term.letRecDecls then
    let declarationIndexes :=
      segment.indexes.filter
        fun index => childIsRawKind segment index `Lean.Parser.Term.letRecDecl
    match declarationIndexes with
    | [] | [_] => []
    | _ :: rest =>
        rest.filterMap fun index => boundaryBreak? segment index 0
  else
    []

def configEntrySequenceBreaks (context : RuleContext) (segment : Segment)
    : List BreakPoint :=
  if parentIsRawKind context `Lean.Elab.ConfigEval.configEntries then
    match nonemptyChildIndexes segment with
    | [] | [_] => []
    | _ :: rest =>
        rest.filterMap fun index => boundaryBreak? segment index 0
  else
    []

def exportBreaks (_context : RuleContext) (segment : Segment) : List BreakPoint :=
  let listBreak :=
    match boundaryBreak? segment 3 1 with
    | some breakPoint => [breakPoint]
    | none => []
  let closeBreak :=
    match segment.indexes.find? fun index => childStartsWithLexeme segment index ")" with
    | some index =>
        match boundaryBreak? segment index 0 with
        | some breakPoint => [breakPoint]
        | none => []
    | none => []
  listBreak ++ closeBreak

/-! ### Applications, signatures, and binders -/

def applicationArgumentStaysAttached
    (context : RuleContext) (segment : Segment) (index : Nat)
    : Bool :=
  attachedBodyStart segment index
  || (childIsRawKind segment index `Lean.Parser.Term.structInst
      && context.ancestors.any
          fun frame => frame.rawKind? == some `Lean.Parser.Command.initialize)

def applicationBreaks (context : RuleContext) (segment : Segment) : List BreakPoint :=
  let patternFunBreaks :=
    (childBoundaryBreaks segment 1).filter
      fun breakPoint =>
        childIsPatternLambdaArgument segment breakPoint.index
  if !patternFunBreaks.isEmpty then
    patternFunBreaks
  else
    (childBoundaryBreaks segment 1).filter
      fun breakPoint =>
        !applicationArgumentStaysAttached context segment breakPoint.index

def applicationHasPatternLambda (_context : RuleContext) (segment : Segment) : Bool :=
  segment.indexes.any fun index => childIsPatternLambdaArgument segment index

def pipeProjBreaks (_context : RuleContext) (segment : Segment) : List BreakPoint :=
  match boundaryBreak? segment 1 0 with
  | some breakPoint => [breakPoint]
  | none => []

def patternAliasParenBreaks (context : RuleContext) (segment : Segment)
    : List BreakPoint :=
  if parentIsRawKind context `Lean.Parser.Term.namedPattern then
    match boundaryBreak? segment 1 2 with
    | some breakPoint => [breakPoint]
    | none => []
  else
    []

def signatureParameterBreaks (context : RuleContext) (segment : Segment)
    : List BreakPoint :=
  let indentLevels :=
    if (parentIsRawKind context `Lean.Parser.Command.optDeclSig
          && grandparentIsRawKind context `Lean.Parser.Command.ctor)
        || parentIsRawKind context `Lean.«command__Unif_hint____Where_|_-⊢__» then
      1
    else
      2
  segment.indexes.filterMap fun index => leadingBreak? segment index indentLevels

def signatureBreaks (context : RuleContext) (segment : Segment) : List BreakPoint :=
  let indentLevels :=
    if parentIsRawKind context `Lean.Parser.Command.ctor
        || parentIsRawKind context `Lean.Parser.Command.structSimpleBinder then
      1
    else
      2
  let typeBreak :=
    match breakBeforeLexeme? segment ":" indentLevels with
    | some breakPoint =>
        match segment.child? breakPoint.index with
        | some child =>
            if treeHasContent child then
              [breakPoint]
            else
              []
        | none => []
    | none => []
  typeBreak

def binderBreaks (_context : RuleContext) (segment : Segment) : List BreakPoint :=
  [breakBeforeLexeme? segment ":" 1].filterMap id

def binderDefaultBreaks (_context : RuleContext) (segment : Segment) : List BreakPoint :=
  [boundaryBreak? segment 1 1].filterMap id

/-! ### Application, signature, and binder rule values -/

def applicationRule : LineBreakRule :=
  {
    name := "application"
    mandatory := applicationHasPatternLambda
    flow := fun _ _ => true
    inheritBase := fun _ _ => false
    breakPoints := applicationBreaks
  }

def pipeProjRule : LineBreakRule :=
  {
    name := "pipeProj"
    flow := fun _ _ => true
    liftsTailIndentation := fun _ _ => true
    breakPoints := pipeProjBreaks
  }

def signatureRule : LineBreakRule :=
  {
    name := "signature"
    inheritBase := fun _ _ => true
    breakPoints := signatureBreaks
  }

def signatureParametersRule : LineBreakRule :=
  {
    name := "signatureParameters"
    flow := fun _ _ => true
    inheritBase := fun _ _ => true
    breakPoints := signatureParameterBreaks
  }

def binderRule : LineBreakRule :=
  {
    name := "binder"
    inheritBase :=
      fun context _ =>
        parentIsSignatureParameters context
        || parentIsRawKind context `Batteries.ExtendedBinder.extBinderCollection
    breakPoints := binderBreaks
  }

def binderDefaultRule : LineBreakRule :=
  {
    name := "binderDefault"
    inheritBase := fun _ _ => true
    breakPoints := binderDefaultBreaks
  }

/-! ### Bindings and `do` syntax -/

def letBreaks (_context : RuleContext) (segment : Segment) : List BreakPoint :=
  match boundaryBreak? segment 4 0 with
  | some breakPoint => [breakPoint]
  | none => []

def letHasExplicitBodySeparator (segment : Segment) : Bool :=
  childStartsWithLexeme segment 3 ";" || childStartsWithLexeme segment 3 "in"

def letBodyCanStartApplicationArgument (segment : Segment) : Bool :=
  match segment.parent with
  | .node (.letExpression _ bodyCanStartApplicationArgument) _ =>
      bodyCanStartApplicationArgument
  | _ => true

def letRecBreaks (_context : RuleContext) (segment : Segment) : List BreakPoint :=
  match boundaryBreak? segment 3 0 with
  | some breakPoint => [breakPoint]
  | none => []

def doLetRecBreaks (_context : RuleContext) (segment : Segment) : List BreakPoint :=
  match segment.child? 1 >>= SyntaxTree.Tree.firstToken? with
  | some token =>
      if SpaceRules.hasLineStructure token.leading.text then
        [boundaryBreak? segment 1 0].filterMap id
      else
        []
  | none => []

def letRecEquationBreaks (_context : RuleContext) (segment : Segment) : List BreakPoint :=
  match firstChildRawKind? segment `Lean.Parser.Term.matchAlts with
  | some index =>
      match boundaryBreak? segment index 1 with
      | some breakPoint => [breakPoint]
      | none => []
  | none => []

def doTryBreaks (_context : RuleContext) (segment : Segment) : List BreakPoint :=
  let bodyBreak := [boundaryBreak? segment 1 1].filterMap id
  let suffixBreaks :=
    segment.indexes.filterMap
      fun index =>
        if 2 <= index then boundaryBreak? segment index 0 else none
  bodyBreak ++ suffixBreaks

def doCatchBreaks (_context : RuleContext) (segment : Segment) : List BreakPoint :=
  match boundaryBreak? segment 4 1 with
  | some breakPoint => [breakPoint]
  | none => []

def doForBreaks (_context : RuleContext) (segment : Segment) : List BreakPoint :=
  [breakAfterLexeme? segment "do" 1].filterMap id

def doFinallyBreaks (_context : RuleContext) (segment : Segment) : List BreakPoint :=
  [breakAfterLexeme? segment "finally" 1].filterMap id

def doForHeaderBreaks (_context : RuleContext) (segment : Segment) : List BreakPoint :=
  [breakBeforeLexeme? segment "in" 2].filterMap id

def doUnlessBreaks (_context : RuleContext) (segment : Segment) : List BreakPoint :=
  [breakAfterLexeme? segment "do" 1].filterMap id

def byTacticBreaks (_context : RuleContext) (segment : Segment) : List BreakPoint :=
  [breakAfterLexeme? segment "by" 1].filterMap id

def fromTermBreaks (_context : RuleContext) (segment : Segment) : List BreakPoint :=
  [delimiterValueBreak? segment "from"].filterMap id

def sufficesBreaks (_context : RuleContext) (segment : Segment) : List BreakPoint :=
  [boundaryBreak? segment 3 0].filterMap id

def haveBreaks (_context : RuleContext) (segment : Segment) : List BreakPoint :=
  [boundaryBreak? segment 4 0].filterMap id

def doIfBreaks (_context : RuleContext) (segment : Segment) : List BreakPoint :=
  let thenBreak :=
    if attachedBodyStart segment 3 then
      none
    else
      boundaryBreak? segment 3 1
  let elseBreaks :=
    (segment.indexes.filter fun index => 4 <= index).filterMap
      fun index =>
        match segment.child? index with
        | some child =>
            if treeHasContent child then boundaryBreak? segment index 0 else none
        | none => none
  [thenBreak].filterMap id ++ elseBreaks

def parentIsDoSequence (context : RuleContext) : Bool :=
  parentIsRawKind context `Lean.Parser.Term.doSeqIndent
  || parentIsRawKind context `Lean.Parser.Term.doSeqBracketed

def doSeqItemBreaks (context : RuleContext) (segment : Segment) : List BreakPoint :=
  if parentIsDoSequence context then
    match nonemptyChildIndexes segment with
    | [] => []
    | [_] => []
    | _ :: rest =>
        rest.filterMap
          fun index =>
            match previousContentIndex? segment index with
            | some previousIndex =>
                match segment.child? previousIndex >>= SyntaxTree.Tree.lastToken? with
                | some token =>
                    if token.lexeme == ";" then none else boundaryBreak? segment index 0
                | none => boundaryBreak? segment index 0
            | none => boundaryBreak? segment index 0
  else
    []

def doSeqSemicolonBreaks (context : RuleContext) (segment : Segment) : List BreakPoint :=
  if parentIsDoSequence context then
    match nonemptyChildIndexes segment with
    | [] | [_] => []
    | _ :: rest =>
        rest.filterMap
          fun index =>
            match previousContentIndex? segment index with
            | some previousIndex =>
                match segment.child? previousIndex >>= SyntaxTree.Tree.lastToken? with
                | some token =>
                    if token.lexeme == ";" then boundaryBreak? segment index 2 else none
                | none => none
            | none => none
  else
    []

def doElseBreaks (context : RuleContext) (segment : Segment) : List BreakPoint :=
  if parentIsRawKind context `Lean.Parser.Term.doIf
      && childStartsWithLexeme segment 0 "else"
      && childIsRawKind segment 1 `Lean.Parser.Term.doSeqIndent then
    match boundaryBreak? segment 1 1 with
    | some breakPoint => [breakPoint]
    | none => []
  else
    []

def doElseIfBreaks (_context : RuleContext) (segment : Segment) : List BreakPoint :=
  if childStartsWithLexeme segment 0 "else"
      && childIsRawKind segment 3 `Lean.Parser.Term.doSeqIndent then
    let thenBreak := boundaryBreak? segment 3 1
    let elseBreaks :=
      (segment.indexes.filter fun index => 4 <= index).filterMap
        fun index =>
          match segment.child? index with
          | some child =>
              if treeHasContent child then boundaryBreak? segment index 0 else none
          | none => none
    [thenBreak].filterMap id ++ elseBreaks
  else
    []

def doElseIfChainBreaks (context : RuleContext) (segment : Segment) : List BreakPoint :=
  if parentIsRawKind context `Lean.Parser.Term.doIf then
    match nonemptyChildIndexes segment with
    | [] | [_] => []
    | first :: rest =>
        if childStartsWithLexeme segment first "else"
            && rest.all fun index => childStartsWithLexeme segment index "else" then
          rest.filterMap fun index => boundaryBreak? segment index 0
        else
          []
  else
    []

def letIdDeclBreaks (context : RuleContext) (segment : Segment) : List BreakPoint :=
  let hasIdentifier :=
    match segment.child? 0 with
    | some identifier => (treeFirstLexeme? identifier).isSome
    | none => false
  let valueBreak := declarationValueBreak? segment
  let valueStartsOnSourceLine :=
    match valueBreak with
    | some breakPoint =>
        match segment.child? breakPoint.index >>= SyntaxTree.Tree.firstToken? with
        | some token => SpaceRules.hasLineStructure token.leading.text
        | none => false
    | none => false
  let returnBreak :=
    if valueStartsOnSourceLine then
      none
    else
      match segment.child? 1 with
      | some parameters =>
          if treeHasContent parameters
              || (hasIdentifier
                  && (grandparentIsRawKind context `Lean.Parser.Term.have
                      || grandparentIsRawKind context `Lean.Parser.Term.haveI)) then
            breakBeforeLexeme? segment ":" 2
          else
            none
      | none => none
  [returnBreak, valueBreak].filterMap id

def letPatternDeclBreaks (_context : RuleContext) (segment : Segment) : List BreakPoint :=
  [breakAfterLexeme? segment ":=" 1].filterMap id

partial def directDoSequenceItemCount : SyntaxTree.Tree → Nat
  | .node (.raw `Lean.Parser.Term.doSeqItem) _ => 1
  | .node (.raw kind) children =>
      if kind == `Lean.Parser.Term.doSeqIndent || kind == `null then
        children.foldl (fun count child => count + directDoSequenceItemCount child) 0
      else
        0
  | .node _ _ => 0
  | .missing | .leaf _ => 0

def childIsNodeKind (segment : Segment) (index : Nat) (kind : SyntaxTree.NodeKind)
    : Bool :=
  match segment.child? index with
  | some (.node childKind _) => childKind == kind
  | _ => false

def doFallbackClauseIndex? (segment : Segment) : Option Nat :=
  segment.indexes.find? fun index => childIsNodeKind segment index .doFallbackClause

def doFallbackClauseBodyRequiresBreak (segment : Segment) (index : Nat) : Bool :=
  match segment.child? index with
  | some (.node .doFallbackClause children) =>
      children[1]?.any fun fallback => 1 < directDoSequenceItemCount fallback
  | _ => false

def doFallbackBodyRequiresBreak (segment : Segment) : Bool :=
  doFallbackClauseIndex? segment
  |>.any fun index => doFallbackClauseBodyRequiresBreak segment index

def doFallbackBreaks (segment : Segment) : List BreakPoint :=
  match doFallbackClauseIndex? segment with
  | some clauseIndex =>
      let clauseBreak := [boundaryBreak? segment clauseIndex 0].filterMap id
      let continuationBreaks :=
        segment.indexes.filterMap
          fun index =>
            if childIsNodeKind segment index .doFallbackContinuation then
              boundaryBreak? segment index 0
            else
              none
      clauseBreak ++ continuationBreaks
  | none => []

def doLetArrowDeclBreaks (_context : RuleContext) (segment : Segment) : List BreakPoint :=
  let valueBreak :=
    if doFallbackBodyRequiresBreak segment then
      none
    else
      match segment.indexes.find?
              fun index => childStartsWithLexeme segment index "←" with
      | some assignmentIndex =>
          match (nonemptyChildIndexes segment).find?
                  fun index => assignmentIndex < index with
          | some rhsIndex => boundaryBreak? segment rhsIndex 1
          | none => none
      | none => none
  [valueBreak].filterMap id ++ doFallbackBreaks segment

def doIdDeclBreaks (context : RuleContext) (segment : Segment) : List BreakPoint :=
  doLetArrowDeclBreaks context segment

def doPatternDeclBreaks (context : RuleContext) (segment : Segment) : List BreakPoint :=
  doLetArrowDeclBreaks context segment

def doLetElseBreaks (_context : RuleContext) (segment : Segment) : List BreakPoint :=
  let valueBreak :=
    if doFallbackBodyRequiresBreak segment then
      none
    else
      breakAfterLexeme? segment ":=" 1
  [valueBreak].filterMap id ++ doFallbackBreaks segment

def doLetExprBreaks (context : RuleContext) (segment : Segment) : List BreakPoint :=
  doLetElseBreaks context segment

def doFallbackClauseBreaks (_context : RuleContext) (segment : Segment)
    : List BreakPoint :=
  match nonemptyChildIndexes segment with
  | _pipeIndex :: fallbackIndex :: _ =>
      [boundaryBreak? segment fallbackIndex 1].filterMap id
  | _ => []

def doFallbackContinuationBreaks (_context : RuleContext) (segment : Segment)
    : List BreakPoint :=
  [leadingBreak? segment segment.start 0].filterMap id

/-! ### Binding and `do` rule values -/

def letRule : LineBreakRule :=
  {
    name := "let"
    mandatory := fun _ _ => true
    -- Put `let` on an indentation column so the RHS and body can both use the
    -- ordinary indentation formulas while still satisfying Lean's layout parser.
    startAlignment :=
      fun _ segment =>
        if letHasExplicitBodySeparator segment
            || !letBodyCanStartApplicationArgument segment then
          .preferred
        else
          .required
    breakPoints := letBreaks
  }

def letRecRule : LineBreakRule :=
  {
    name := "letRec"
    mandatory := fun _ _ => true
    startAlignment :=
      fun _ segment =>
        if letBodyCanStartApplicationArgument segment then .required else .preferred
    breakPoints := letRecBreaks
  }

def doLetRecRule : LineBreakRule :=
  {
    name := "doLetRec"
    mandatory := fun context segment => !(doLetRecBreaks context segment).isEmpty
    inheritBase := fun _ _ => true
    breakPoints := doLetRecBreaks
  }

def letIdDeclRule : LineBreakRule :=
  {
    name := "letIdDecl"
    flow :=
      fun _ segment =>
        (contentIndexAfterLexeme? segment ":=").any
          fun index => attachedBodyStart segment index
    inheritBase := fun _ _ => true
    roundUpBaseIndentation := true
    breakPoints := letIdDeclBreaks
  }

def letPatternDeclRule : LineBreakRule :=
  {
    name := "letPatternDecl"
    inheritBase := fun _ _ => true
    roundUpBaseIndentation := true
    breakPoints := letPatternDeclBreaks
  }

def doLetRule : LineBreakRule :=
  {
    name := "doLet"
    inheritBase := fun _ _ => true
  }

def byTacticRule : LineBreakRule :=
  {
    name := "byTactic"
    useExistingBreaks :=
      fun context _ =>
        parentIsRawKind context `Lean.Parser.Term.basicFun
        || attachedBodyFollowsDelimiter context ";"
    inheritBase := fun _ _ => true
    breakPoints := byTacticBreaks
  }

def doLetElseRule : LineBreakRule :=
  {
    name := "doLetElse"
    flow := fun _ _ => true
    inheritBase := fun _ _ => true
    breakPoints := doLetElseBreaks
  }

def doLetExprRule : LineBreakRule :=
  {
    name := "doLetExpr"
    mandatory := fun _ _ => true
    inheritBase := fun _ _ => true
    breakPoints := doLetExprBreaks
  }

def doFallbackClauseRule : LineBreakRule :=
  {
    name := "doFallbackClause"
    formatOriginalChildLeadingBoundary :=
      fun _ segment index => segment.start < index
    keepPrefixWithChildFirstLine := fun _ segment index => segment.start < index
    flow := fun _ _ => true
    inheritBase := fun _ _ => true
    breakPoints := doFallbackClauseBreaks
  }

def doFallbackContinuationRule : LineBreakRule :=
  {
    name := "doFallbackContinuation"
    mandatory := fun _ _ => true
    inheritBase := fun _ _ => true
    breakPoints := doFallbackContinuationBreaks
  }

def doSeqIndentRule : LineBreakRule :=
  {
    name := "doSeqIndent"
    inheritBase := fun context _ => inDoLetFallback context
  }

def doIdDeclRule : LineBreakRule :=
  {
    name := "doIdDecl"
    flow := fun _ _ => true
    inheritBase := fun _ _ => true
    breakPoints := doIdDeclBreaks
  }

def doPatternDeclRule : LineBreakRule :=
  {
    name := "doPatternDecl"
    flow := fun _ _ => true
    inheritBase := fun _ _ => true
    breakPoints := doPatternDeclBreaks
  }

def dbgTraceRule : LineBreakRule :=
  {
    name := "dbgTrace"
    useExistingBreaks := fun _ _ => true
    breakPoints := fun _ segment => [boundaryBreak? segment 3 0].filterMap id
  }

/-! ### Declaration suffixes and recursive declarations -/

def baseAlignedTrailingClauseBreaks (segment : Segment) : List BreakPoint :=
  match nonemptyChildIndexes segment with
  | [] => []
  | firstIndex :: rest =>
      [leadingBreak? segment firstIndex 0].filterMap id
      ++ rest.filterMap fun index => boundaryBreak? segment index 0

def whereDeclsBreaks (_context : RuleContext) (segment : Segment) : List BreakPoint :=
  let leading :=
    match leadingBreak? segment segment.start 0 with
    | some breakPoint => [breakPoint]
    | none => []
  let bodyIndexes := (nonemptyChildIndexes segment).drop 1
  let body :=
    bodyIndexes.filterMap
      fun index =>
        if childStartsWithLexeme segment index "finally" then
          if bodyIndexes.head? == some index then
            none
          else
            boundaryBreak? segment index 0
        else
          boundaryBreak? segment index 1
  leading ++ body

def whereFinallyBreaks (_context : RuleContext) (segment : Segment) : List BreakPoint :=
  [boundaryBreak? segment 1 1].filterMap id

def whereStructInstBreaks (_context : RuleContext) (segment : Segment)
    : List BreakPoint :=
  let fieldBreak := [boundaryBreak? segment 1 1].filterMap id
  let trailingWhereBreaks :=
    segment.indexes.filterMap
      fun index =>
        if 1 < index
            && childIsRawKindThroughNullWrappers
                segment index `Lean.Parser.Term.whereDecls then
          boundaryBreak? segment index 0
        else
          none
  fieldBreak ++ trailingWhereBreaks

def terminationSuffixBreaks (_context : RuleContext) (segment : Segment)
    : List BreakPoint :=
  baseAlignedTrailingClauseBreaks segment

def terminationByBreaks (_context : RuleContext) (segment : Segment) : List BreakPoint :=
  match (nonemptyChildIndexes segment).getLast? with
  | some measureIndex =>
      match boundaryBreak? segment measureIndex 1 with
      | some breakPoint => [breakPoint]
      | none => []
  | none => []

def decreasingByBreaks (_context : RuleContext) (segment : Segment) : List BreakPoint :=
  [boundaryBreak? segment 1 1].filterMap id

def setOptionBreaks (_context : RuleContext) (segment : Segment) : List BreakPoint :=
  match breakAfterLexeme? segment "in" 0 with
  | some breakPoint => [breakPoint]
  | none => []

/-! ### Declaration-suffix rule values -/

def whereDeclsRule : LineBreakRule :=
  {
    name := "whereDecls"
    useExistingBreaks := fun _ _ => true
    inheritBase := fun _ _ => true
    breakPoints := whereDeclsBreaks
  }

def whereFinallyRule : LineBreakRule :=
  {
    name := "whereFinally"
    mandatory := fun context segment => !(whereFinallyBreaks context segment).isEmpty
    breakPoints := whereFinallyBreaks
  }

def whereStructInstRule : LineBreakRule :=
  {
    name := "whereStructInst"
    useExistingBreaks := fun _ _ => true
    inheritBase := fun _ _ => true
    breakPoints := whereStructInstBreaks
  }

def terminationSuffixRule : LineBreakRule :=
  {
    name := "terminationSuffix"
    useExistingBreaks := fun _ _ => true
    inheritBase := fun _ _ => true
    breakPoints := terminationSuffixBreaks
  }

def terminationByRule : LineBreakRule :=
  {
    name := "terminationBy"
    useExistingBreaks := fun _ _ => true
    flow := fun _ _ => true
    inheritBase := fun _ _ => true
    breakPoints := terminationByBreaks
  }

def decreasingByRule : LineBreakRule :=
  {
    name := "decreasingBy"
    useExistingBreaks := fun _ _ => true
    inheritBase := fun _ _ => true
    breakPoints := decreasingByBreaks
  }

def rawDefinitionBreaks (_context : RuleContext) (segment : Segment) : List BreakPoint :=
  let valueBreak :=
    if childStartsWithSuffixKeywordToken segment 3 then
      []
    else
      [boundaryBreak? segment 3 1].filterMap id
  valueBreak ++ declarationTrailingClauseBreaks segment

def declarationEquationBreaks (segment : Segment) : List BreakPoint :=
  match firstChildRawKind? segment `Lean.Parser.Command.declValEqns with
  | some index => [boundaryBreak? segment index 1].filterMap id
  | none => []

def theoremBreaks (_context : RuleContext) (segment : Segment) : List BreakPoint :=
  [declarationValueBreak? segment].filterMap id
  ++ declarationEquationBreaks segment
  ++ declarationTrailingClauseBreaks segment

def inductiveBreaks (context : RuleContext) (segment : Segment) : List BreakPoint :=
  let alternativeBreaks :=
    segment.indexes.filterMap
      fun index =>
        if childStartsWithLexeme segment index "|" then
          boundaryBreak? segment index 1
        else
          none
  alternativeBreaks ++ derivingBreaks context segment

/-! ### Declaration and collection rule values -/

def annotatedDeclarationRule : LineBreakRule :=
  {
    name := "annotatedDeclaration"
    keepPrefixWithChildFirstLine :=
      fun _ segment index => annotatedDeclarationKeepsModifierPrefix segment index
    useExistingBreaks := fun _ _ => true
    flow := fun context segment => !(annotatedDeclarationBreaks context segment).isEmpty
    inheritBase :=
      fun _ segment =>
        treeContainsRawKind `Lean.Parser.Command.structCtor segment.parent
    breakPoints := annotatedDeclarationBreaks
  }

def declarationModifierRule : LineBreakRule :=
  {
    name := "declarationModifier"
    useExistingBreaks := fun _ _ => true
    breakPoints := declarationModifierBreaks
  }

def declarationIdentifierRule : LineBreakRule :=
  {
    name := "declarationIdentifier"
    flow := fun _ _ => true
    inheritBase := fun _ _ => true
    breakPoints :=
      fun _ segment =>
        segment.indexes.filterMap fun index => leadingBreak? segment index 2
  }

def derivingClauseRule : LineBreakRule :=
  {
    name := "derivingClause"
    flow := fun _ _ => true
    inheritBase := fun _ _ => true
    breakPoints := derivingClauseBreaks
  }

def unifConstraintsRule : LineBreakRule :=
  {
    name := "unifConstraints"
    mandatory := fun _ segment => 1 < segment.size
    breakPoints := fun _ segment => childBoundaryBreaks segment 0
  }

def structureRule : LineBreakRule :=
  {
    name := "structure"
    inheritBase :=
      fun context _ =>
        match context.ancestors with
        | parent :: _ =>
            (List.range parent.childIndex).any
              fun index => parent.segment.parentChild? index |>.any treeHasContent
        | [] => false
  }

def structureHeaderRule : LineBreakRule :=
  {
    name := "structureHeader"
    useExistingBreaks := fun _ _ => true
    flow := fun context segment => !(structureHeaderBreaks context segment).isEmpty
    inheritBase := fun _ _ => true
    breakPoints := structureHeaderBreaks
  }

def structureConstructorRule : LineBreakRule :=
  {
    name := "structureConstructor"
    mandatory :=
      fun context segment => !(structureConstructorBreaks context segment).isEmpty
    inheritBase := fun _ _ => true
    breakPoints := structureConstructorBreaks
  }

def structureDerivingRule : LineBreakRule :=
  {
    name := "structureDeriving"
    mandatory :=
      fun context segment => !(structureDerivingBreaks context segment).isEmpty
    inheritBase := fun _ _ => true
    breakPoints := structureDerivingBreaks
  }

def exportRule : LineBreakRule :=
  {
    name := "export"
    breakPoints := exportBreaks
  }

def assertNotExistsRule : LineBreakRule :=
  {
    name := "assertNotExists"
    useExistingBreaks := fun _ _ => true
    breakPoints := assertNotExistsBreaks
  }

def definitionRule : LineBreakRule :=
  {
    name := "definition"
    keepPrefixWithChildFirstLine :=
      fun _ segment index =>
        childIsRawKind segment index `Lean.Parser.Command.whereStructInst
    useExistingBreaks := fun _ _ => true
    inheritBase := fun _ _ => true
    breakPoints := definitionBreaks
  }

def rawDefinitionRule : LineBreakRule :=
  {
    name := "rawDefinition"
    inheritBase := fun _ _ => true
    breakPoints := rawDefinitionBreaks
  }

def theoremRule : LineBreakRule :=
  {
    name := "theorem"
    useExistingBreaks := fun _ _ => true
    inheritBase := fun _ _ => true
    breakPoints := theoremBreaks
  }

def structInstRule : LineBreakRule :=
  {
    name := "structInst"
    inheritBase := fun _ _ => true
    liftsTailIndentation :=
      fun _ segment =>
        structInstHasWith segment && !structInstHasMultipleUpdateSources segment
    roundUpBaseIndentation := true
    breakPoints := structInstBreaks
  }

def bracedTermBreaks (context : RuleContext) (segment : Segment) : List BreakPoint :=
  let structureBreaks := structInstBreaks context segment
  if structureBreaks.isEmpty then delimitedCollectionBreaks segment else structureBreaks

def bracedTermRule : LineBreakRule :=
  {
    name := "bracedTerm"
    inheritBase := fun _ segment => 1 < delimitedItemCount segment
    liftsTailIndentation :=
      fun _ segment =>
        structInstHasWith segment && !structInstHasMultipleUpdateSources segment
    roundUpBaseIndentation := true
    breakPoints := bracedTermBreaks
  }

def structureUpdateRule : LineBreakRule :=
  {
    name := "structureUpdate"
    useExistingBreaks := fun _ _ => true
    liftsTailIndentation :=
      fun _ segment => (structureUpdateSourceIndexes segment).length <= 1
    breakPoints := structureUpdateBreaks
  }

def typeAscriptionRule : LineBreakRule :=
  {
    name := "typeAscription"
    liftsTailIndentation := fun _ _ => true
    breakPoints := typeAscriptionBreaks
  }

def namedArgumentRule : LineBreakRule :=
  {
    name := "namedArgument"
    keepPrefixWithChildFirstLine := fun _ _ index => index == 4
    flow := fun _ _ => true
    breakPoints := namedArgumentBreaks
  }

def tupleRule : LineBreakRule :=
  {
    name := "tuple"
    inheritBase := fun _ _ => true
    roundUpBaseIndentation := true
    breakPoints := tupleBreaks
  }

def anonymousCtorRule : LineBreakRule :=
  {
    name := "anonymousCtor"
    inheritBase := fun _ segment => 1 < anonymousCtorItemCount segment
    roundUpBaseIndentation := true
    breakPoints := anonymousCtorBreaks
  }

def setBuilderRule : LineBreakRule :=
  {
    name := "setBuilder"
    useExistingBreaks := fun _ _ => true
    roundUpBaseIndentation := true
    breakPoints := setBuilderBreaks
  }

def bracketedRelationBreaks (_context : RuleContext) (segment : Segment)
    : List BreakPoint :=
  match nonemptyChildIndexes segment with
  | [_, operatorIndex, _, _, rhsIndex] =>
      [
        boundaryBreak? segment operatorIndex 1,
        boundaryBreak? segment rhsIndex 1
      ].filterMap
        id
  | _ => []

def bracketedRelationRule : LineBreakRule :=
  {
    name := "bracketedRelation"
    useExistingBreaks := fun _ _ => true
    flow := fun _ _ => true
    breakPoints := bracketedRelationBreaks
  }

def indexedNotationBreaks (_context : RuleContext) (segment : Segment)
    : List BreakPoint :=
  match segment.parent, nonemptyChildIndexes segment with
  | .node (.indexedInfix _) _, [_, operatorIndex, _, _, rhsIndex] =>
      [
        boundaryBreak? segment operatorIndex 1,
        boundaryBreak? segment rhsIndex 1
      ].filterMap
        id
  | _, _ => []

def indexedNotationRule : LineBreakRule :=
  {
    name := "indexedNotation"
    useExistingBreaks := fun _ _ => true
    flow := fun _ _ => true
    breakPoints := indexedNotationBreaks
  }

def indexedTermBreaks (_context : RuleContext) (segment : Segment) : List BreakPoint :=
  let indexes := nonemptyChildIndexes segment
  match indexes.find? fun index => childAtomLexemeEndsWith segment index "[" with
  | some openingIndex =>
      match indexes.find?
              fun index =>
                openingIndex < index && childIsAtomLexeme segment index "]" with
      | some closingIndex =>
          indexes.filterMap
            fun index =>
              if (openingIndex < index
                    && index < closingIndex
                    && !childIsTrailingSeparator segment index)
                  || closingIndex < index then
                boundaryBreak? segment index 1
              else
                none
      | none => []
  | none => []

def indexedTermRule : LineBreakRule :=
  {
    name := "indexedTerm"
    useExistingBreaks := fun _ _ => true
    flow := fun _ _ => true
    breakPoints := indexedTermBreaks
  }

def isGeneratedTermKind (kind : Lean.SyntaxNodeKind) : Bool :=
  let name := toString kind
  name.startsWith "«term" || SpaceRules.containsSubstring name ".«term"

def isGeneratedIndexedPrefixTerm
    (kind : Lean.SyntaxNodeKind) (children : Array SyntaxTree.Tree)
    : Bool :=
  if !isGeneratedTermKind kind then
    false
  else
    let segment := Segment.ofTree (.node (.raw kind) children)
    match (nonemptyChildIndexes segment).head? with
    | some openingIndex =>
        if !childAtomLexemeEndsWith segment openingIndex "[" then
          false
        else
          match (nonemptyChildIndexes segment).find?
                  fun index =>
                    openingIndex < index && childIsAtomLexeme segment index "]" with
          | some closingIndex =>
              (nonemptyChildIndexes segment).any fun index => closingIndex < index
          | none => false
    | none => false

def isSymmetricDelimitedGeneratedTerm
    (kind : Lean.SyntaxNodeKind) (children : Array SyntaxTree.Tree)
    : Bool :=
  if !isGeneratedTermKind kind then
    false
  else
    match (children.filter fun child => child.firstToken?.isSome).toList with
    | [opening, _, closing] =>
        match opening.firstToken?, closing.lastToken? with
        | some opening, some closing =>
            opening.role == .atom
            && closing.role == .atom
            && opening.lexeme == closing.lexeme
        | _, _ => false
    | _ => false

def isGeneratedPostfixTerm (kind : Lean.SyntaxNodeKind) (children : Array SyntaxTree.Tree)
    : Bool :=
  if !isGeneratedTermKind kind then
    false
  else
    match (children.filter fun child => child.firstToken?.isSome).toList with
    | [_, .leaf token] => token.role == .atom
    | _ => false

def isGeneratedLocalNotationKind (kind : Lean.SyntaxNodeKind) : Bool :=
  (toString kind).endsWith "Local≺»"

def structInstFieldsRule : LineBreakRule :=
  {
    name := "structInstFields"
    inheritBase := fun _ _ => true
  }

def structInstFieldRule : LineBreakRule :=
  {
    name := "structInstField"
    useExistingBreaks := fun _ _ => true
    breakPoints := structInstFieldBodyBreaks
  }

def structFieldsRule : LineBreakRule :=
  {
    name := "structFields"
    mandatory := fun context segment => !(structFieldsBreaks context segment).isEmpty
    inheritBase := fun _ _ => true
    breakPoints := structFieldsBreaks
  }

def structCtorRule : LineBreakRule :=
  { name := "structCtor" }

def inductiveRule : LineBreakRule :=
  {
    name := "inductive"
    mandatory := fun context segment => !(inductiveBreaks context segment).isEmpty
    useExistingBreaks := fun _ _ => true
    breakPoints := inductiveBreaks
  }

def mutualBreaks (_context : RuleContext) (segment : Segment) : List BreakPoint :=
  let bodyBreak :=
    match boundaryBreak? segment 1 1 with
    | some breakPoint => [breakPoint]
    | none => []
  let endBreak :=
    match segment.indexes.find?
            fun index => childStartsWithLexeme segment index "end" with
    | some index =>
        match boundaryBreak? segment index 0 with
        | some breakPoint => [breakPoint]
        | none => []
    | none => []
  bodyBreak ++ endBreak

/-! ### Conditionals, matches, functions, and quantifiers -/

def ifThenElseBreaks (_context : RuleContext) (segment : Segment) : List BreakPoint :=
  [(3, 1), (4, 0), (5, 1)].filterMap
    fun (index, indentLevels) =>
      if attachedBodyStart segment index then
        none
      else
        boundaryBreak? segment index indentLevels

def dependentIfThenElseBreaks (_context : RuleContext) (segment : Segment)
    : List BreakPoint :=
  [(3, 1), (5, 1), (6, 0), (7, 1)].filterMap
    fun (index, indentLevels) =>
      if attachedBodyStart segment index then
        none
      else
        boundaryBreak? segment index indentLevels

def ifLetThenElseBreaks (_context : RuleContext) (segment : Segment) : List BreakPoint :=
  [(6, 1), (7, 0), (8, 1)].filterMap
    fun (index, indentLevels) =>
      if attachedBodyStart segment index then
        none
      else
        boundaryBreak? segment index indentLevels

def ifThenElseChainBreaks (_context : RuleContext) (segment : Segment)
    : List BreakPoint :=
  (List.range (segment.size - 1)).filterMap
    fun offset =>
      let index := segment.start + offset + 1
      let indentLevels := if offset % 2 == 0 then 1 else 0
      boundaryBreak? segment index indentLevels

def firstMatchAlternativesIndex? (segment : Segment) : Option Nat :=
  match firstChildRawKind? segment `Lean.Parser.Term.matchAlts with
  | some index => some index
  | none => firstChildRawKind? segment `Lean.Parser.Term.matchExprAlts

def matchExpressionBreaks (_context : RuleContext) (segment : Segment)
    : List BreakPoint :=
  match firstMatchAlternativesIndex? segment with
  | some index =>
      match boundaryBreak? segment index 0 with
      | some breakPoint => [breakPoint]
      | none => []
  | none => []

def quantifierBodyIndex? (segment : Segment) : Option Nat :=
  let contentIndexes :=
    segment.parentIndexes.filter
      fun index =>
        match segment.parentChild? index with
        | some child => treeHasContent child
        | none => false
  let separatorIndex? :=
    (contentIndexes.filter fun index => childStartsWithLexeme segment index ",").getLast?
  match separatorIndex? with
  | some separatorIndex =>
      contentIndexes.find? fun index => separatorIndex < index
  | none => contentIndexes.getLast?

def quantifierBreaks (_context : RuleContext) (segment : Segment) : List BreakPoint :=
  match quantifierBodyIndex? segment with
  | some bodyIndex =>
      let bodyIsSameQuantifier :=
        match segment.parent, segment.child? bodyIndex with
        | .node (.raw kind) _, some (.node (.raw childKind) _) => childKind == kind
        | _, _ => false
      match boundaryBreak? segment bodyIndex (if bodyIsSameQuantifier then 0 else 1) with
      | some breakPoint => [breakPoint]
      | none => []
  | none => []

def basicFunBreaks (_context : RuleContext) (segment : Segment) : List BreakPoint :=
  if attachedBodyStart segment 3 then
    []
  else
    match boundaryBreak? segment 3 1 with
    | some breakPoint => [breakPoint]
    | none => []

def subtypeBreaks (_context : RuleContext) (segment : Segment) : List BreakPoint :=
  match boundaryBreak? segment 3 1 with
  | some breakPoint => [breakPoint]
  | none => []

def inMatchAltRhs (context : RuleContext) : Bool :=
  match context.ancestors with
  | parent :: grandparent :: _ =>
      (parent.rawKind? == some `Lean.Parser.Term.matchAlt && parent.childIndex == 3)
      || (parent.rawKind? == some `null
          && grandparent.rawKind? == some `Lean.Parser.Term.matchAlt
          && grandparent.childIndex == 3)
  | parent :: _ =>
      parent.rawKind? == some `Lean.Parser.Term.matchAlt && parent.childIndex == 3
  | _ => false

def attachedBodyHasFollowingApplicationArgument (context : RuleContext) : Bool :=
  match context.ancestors with
  | parent :: _ =>
      parent.nodeKind? == some .application
      && parent.segment.indexes.any
          fun index =>
            parent.childIndex < index && (parent.segment.child? index).any treeHasContent
  | _ => false

def matchAltBreaks (_context : RuleContext) (segment : Segment) : List BreakPoint :=
  if childIsRawKind segment 3 `Lean.Parser.Term.byTactic
      || attachedBodyStart segment 3 then
    []
  else
    match boundaryBreak? segment 3 alternativeBodyIndentLevels with
    | some breakPoint => [breakPoint]
    | none => []

def matchExprAltBreaks (_context : RuleContext) (segment : Segment) : List BreakPoint :=
  [leadingBreak? segment segment.start 0, boundaryBreak? segment 3 1].filterMap id

def doBreaks (context : RuleContext) (segment : Segment) : List BreakPoint :=
  let indentLevels :=
    if inMatchAltRhs context then
      alternativeBodyIndentLevels
    else if attachedBodyHasFollowingApplicationArgument context then
      2
    else
      1
  match boundaryBreak? segment 1 indentLevels with
  | some breakPoint => [breakPoint]
  | none => []

def matchAltsWhereDeclsBreaks (_context : RuleContext) (segment : Segment)
    : List BreakPoint :=
  let leading := [leadingBreak? segment segment.start 0].filterMap id
  let trailingClauses :=
    terminationSuffixChildBreaks segment
    ++ segment.indexes.filterMap
        fun index =>
          if childStartsWithLexeme segment index "where" then
            boundaryBreak? segment index 0
          else
            none
  leading ++ trailingClauses

def matchAltsBreaks (_context : RuleContext) (segment : Segment) : List BreakPoint :=
  segment.indexes.filterMap fun index => leadingBreak? segment index 0

/-! ### Infix expressions and generic wrappers -/

def barSeparatedSequence (segment : Segment) : Bool :=
  let indexes := nonemptyChildIndexes segment
  3 <= indexes.length
  && indexes.length % 2 == 1
  && indexes.zipIdx.all
      fun (index, offset) =>
        if offset % 2 == 1 then
          childStartsWithLexeme segment index "|"
        else
          !childStartsWithLexeme segment index "|"

def childIsBarSeparatedSequence (segment : Segment) (index : Nat) : Bool :=
  match segment.child? index with
  | some tree@(.node (.raw `null) _) =>
      barSeparatedSequence (Segment.ofTree tree)
  | _ => false

def infixAlternativeRhsBreak? (segment : Segment) : Option BreakPoint := do
  let rhsIndex ← (nonemptyChildIndexes segment).getLast?
  if childIsBarSeparatedSequence segment rhsIndex then
    boundaryBreak? segment rhsIndex 1
  else
    none

def infixBreaks (_context : RuleContext) (segment : Segment) : List BreakPoint :=
  if lowPriorityInfixSegment segment then
    segment.indexes.filterMap
      fun index =>
        if segment.start < index && childIsLowPriorityInfixRhs segment index then
          boundaryBreak? segment index 0
        else
          none
  else
    match segment.parent with
    | .node (.infixChain `Lean.Parser.Term.proj) _ => []
    | _ =>
        match segment.children? with
        | none => []
        | some children =>
            (List.range children.size).flatMap
              fun index =>
                if index % 2 == 1 then
                  [boundaryBreak? segment index 0].filterMap id
                else
                  []

def lowPriorityInfixRhsBreaks (_context : RuleContext) (segment : Segment)
    : List BreakPoint :=
  if lowPriorityInfixRhsHasAttachedBody segment
      && !lowPriorityInfixRhsHasMandatoryAlignedBody segment then
    []
  else
    [boundaryBreak? segment (segment.start + 1) 1].filterMap id

def infixRuleBreaks (context : RuleContext) (segment : Segment) : List BreakPoint :=
  let breaks :=
    infixBreaks context segment ++ [infixAlternativeRhsBreak? segment].filterMap id
  if infixAttachedBodyAssignmentValue context segment then
    breaks.map
      fun breakPoint =>
        { breakPoint with indentLevels := breakPoint.indentLevels + 1 }
  else
    breaks

def commandInBreaks (_context : RuleContext) (segment : Segment) : List BreakPoint :=
  segment.indexes.filterMap
    fun index =>
      if index == segment.start then
        none
      else if childStartsWithLexeme segment (index - 1) "in" then
        boundaryBreak? segment index 0
      else
        none

def arrowInfixSegment (segment : Segment) : Bool :=
  match segment.parent with
  | .node (.infixChain `Lean.Parser.Term.arrow) _ => true
  | _ => false

def logicalOperatorLexeme (lexeme : String) : Bool :=
  lexeme == "->"
  || lexeme == "→"
  || lexeme == "∧"
  || lexeme == "∨"
  || lexeme == "/\\"
  || lexeme == "\\/"
  || lexeme == "="

def segmentHasLogicalOperator (segment : Segment) : Bool :=
  match segment.parent with
  | .node (.infixChain _) _ =>
      segment.parentIndexes.any
        fun index =>
          index % 2 == 1
          && match segment.parentChild? index >>= treeFirstLexeme? with
              | some lexeme => logicalOperatorLexeme lexeme
              | none => false
  | _ => false

def signatureReturnContainsProp (tree : SyntaxTree.Tree) : Bool :=
  match tree with
  | .node (.raw `Lean.Parser.Command.optDeclSig) children
  | .node (.raw `Lean.Parser.Command.declSig) children =>
      match children[1]? with
      | some returnTree => treeContainsLexeme "Prop" returnTree
      | none => false
  | _ => false

def segmentIsPropDefinitionBody (segment : Segment) (childIndex : Nat) : Bool :=
  match segment.parent with
  | .node .definition _ =>
      childIndex == 4
      && match segment.parentChild? 2 with
          | some signature => signatureReturnContainsProp signature
          | none => false
  | _ => false

def frameIsTheoremContext (frame : Frame) : Bool :=
  match frame.segment.parent with
  | .node (.raw `Lean.Parser.Command.theorem) _ => true
  | .node (.raw `lemma) _ => true
  | .node (.raw `group) _ => treeFirstLexeme? frame.segment.parent == some "lemma"
  | _ => false

def frameIsQuantifierBody (frame : Frame) : Bool :=
  treeIsBinderOperatorTerm frame.segment.parent
  && quantifierBodyIndex? frame.segment == some frame.childIndex

def frameIsLogicalContext (frame : Frame) : Bool :=
  frameIsTheoremContext frame
  || segmentIsPropDefinitionBody frame.segment frame.childIndex
  || frameIsQuantifierBody frame
  || segmentHasLogicalOperator frame.segment

def framesContainLogicalContext : List Frame → Bool
  | [] => false
  | frame :: rest => frameIsLogicalContext frame || framesContainLogicalContext rest

def arrowInfixLogicalContext (context : RuleContext) : Bool :=
  framesContainLogicalContext context.ancestors

def infixFlow (context : RuleContext) (segment : Segment) : Bool :=
  lowPriorityInfixAllRhsCanFlow segment
  || (arrowInfixSegment segment && !arrowInfixLogicalContext context)

def infixAlternativeSequence (context : RuleContext) (segment : Segment) : Bool :=
  barSeparatedSequence segment
  && match context.ancestors with
      | parent :: _ =>
          parent.nodeKind?.any
            fun
            | .infixChain _ =>
                (nonemptyChildIndexes parent.segment).getLast? == some parent.childIndex
            | _ => false
      | [] => false

def infixAlternativeBreaks (context : RuleContext) (segment : Segment)
    : List BreakPoint :=
  if infixAlternativeSequence context segment then
    segment.indexes.filterMap
      fun index =>
        if childStartsWithLexeme segment index "|" then
          boundaryBreak? segment index 0
        else
          none
  else
    []

def bigOperatorBreaks (_context : RuleContext) (segment : Segment) : List BreakPoint :=
  [breakAfterLexeme? segment "," 1].filterMap id

def binderTacticBreaks (_context : RuleContext) (segment : Segment) : List BreakPoint :=
  [breakBeforeLexeme? segment "by" 2].filterMap id

def simpsProjectionRuleBreaks (context : RuleContext) (segment : Segment)
    : List BreakPoint :=
  if hasRawKindAncestor context `Lean.Parser.Command.simpsProj then
    (nonemptyChildIndexes segment).filterMap
      fun index =>
        match previousContentIndex? segment index with
        | some previousIndex =>
            if childStartsWithLexeme segment previousIndex "," then
              boundaryBreak? segment index 1
            else
              none
        | none => none
  else
    []

def nullBreaks (context : RuleContext) (segment : Segment) : List BreakPoint :=
  structureFieldBreaks context segment
  ++ structureParentBreaks context segment
  ++ structInstFieldBreaks context segment
  ++ inductiveAlternativeBreaks context segment
  ++ tacticAlternativeSequenceBreaks context segment
  ++ tacticSequenceItemBreaks context segment
  ++ quantifierBinderBreaks context segment
  ++ extendedBinderCollectionBreaks context segment
  ++ binderIdentifierBreaks context segment
  ++ commandBinderBreaks context segment
  ++ openIdentifierBreaks context segment
  ++ commandAttributeIdentifierBreaks context segment
  ++ allowUnusedTacticIdentifierBreaks context segment
  ++ assertNotExistsIdentifierBreaks context segment
  ++ exportItemBreaks context segment
  ++ doSeqItemBreaks context segment
  ++ doSeqSemicolonBreaks context segment
  ++ infixAlternativeBreaks context segment
  ++ doElseBreaks context segment
  ++ doElseIfBreaks context segment
  ++ doElseIfChainBreaks context segment
  ++ moduleImportBreaks context segment
  ++ moduleCommandBreaks context segment
  ++ mutualCommandBreaks context segment
  ++ letRecDeclarationSequenceBreaks context segment
  ++ configEntrySequenceBreaks context segment
  ++ simpsProjectionRuleBreaks context segment

def nullBreaksMandatory (context : RuleContext) (segment : Segment) : Bool :=
  !(structureFieldBreaks context segment).isEmpty
  || structInstFieldsMandatory context segment
  || !(inductiveAlternativeBreaks context segment).isEmpty
  || !(tacticAlternativeSequenceBreaks context segment).isEmpty
  || !(tacticSequenceItemBreaks context segment).isEmpty
  || !(doSeqItemBreaks context segment).isEmpty
  || !(doElseBreaks context segment).isEmpty
  || !(doElseIfBreaks context segment).isEmpty
  || !(doElseIfChainBreaks context segment).isEmpty
  || !(moduleImportBreaks context segment).isEmpty
  || !(moduleCommandBreaks context segment).isEmpty
  || !(mutualCommandBreaks context segment).isEmpty
  || !(letRecDeclarationSequenceBreaks context segment).isEmpty
  || !(configEntrySequenceBreaks context segment).isEmpty

-----------------------------------------------------------------------------------------
-- Rule values
-----------------------------------------------------------------------------------------

/-! ### Generic and wrapper rule values -/

def nullRule : LineBreakRule :=
  {
    name := "null"
    mandatory := nullBreaksMandatory
    flow :=
      fun context segment =>
        !(structureParentBreaks context segment).isEmpty
        || !(quantifierBinderBreaks context segment).isEmpty
        || !(extendedBinderCollectionBreaks context segment).isEmpty
        || !(binderIdentifierBreaks context segment).isEmpty
        || !(commandBinderBreaks context segment).isEmpty
        || !(openIdentifierBreaks context segment).isEmpty
        || !(commandAttributeIdentifierBreaks context segment).isEmpty
        || !(allowUnusedTacticIdentifierBreaks context segment).isEmpty
        || !(assertNotExistsIdentifierBreaks context segment).isEmpty
        || !(exportItemBreaks context segment).isEmpty
        || !(infixAlternativeBreaks context segment).isEmpty
    inheritBase := nullInheritBase
    breakPoints := nullBreaks
  }

def arrayRule : LineBreakRule :=
  {
    name := "array"
    useExistingBreaks :=
      fun _ segment => segment.rawKind? == some `«term#[_,]»
    inheritBase :=
      fun _ segment =>
        segment.rawKind? == some `«term#[_,]» || 1 < arrayItemCount segment
    roundUpBaseIndentation := true
    breakPoints := arrayBreaks
  }

def declarationRule : LineBreakRule :=
  { name := "declaration" }

def commandAttributeRule : LineBreakRule :=
  { name := "commandAttribute" }

def variableCommandRule : LineBreakRule :=
  { name := "variableCommand" }

def instanceRule : LineBreakRule :=
  {
    name := "instance"
    inheritBase := fun _ _ => true
    breakPoints := fun _ segment => declarationEquationBreaks segment
  }

def declarationValueRule : LineBreakRule :=
  {
    name := "declarationValue"
    mandatory :=
      fun _ segment =>
        declarationValueHasAttachedBodyInfix segment
        || declarationValueHasNestedProofBody segment
    inheritBase := fun _ _ => true
    breakPoints := declarationValueBreaks
  }

def notationHeaderGroupBreak? (segment : Segment) : Option BreakPoint := do
  let arrowIndex ←
    segment.indexes.find? fun index => childStartsWithLexeme segment index "=>"
  let headerIndex ← previousContentIndex? segment arrowIndex
  let header ← segment.child? headerIndex
  match header with
  | .node (.raw `null) children =>
      if 1 < (children.filter fun child => child.firstToken?.isSome).size then
        boundaryBreak? segment headerIndex 1
      else
        none
  | _ => none

def notationBreaks (_context : RuleContext) (segment : Segment) : List BreakPoint :=
  [notationHeaderGroupBreak? segment, breakAfterLexeme? segment "=>" 1].filterMap id

def notationRule : LineBreakRule :=
  {
    name := "notation"
    useExistingBreaks := fun _ _ => true
    flow :=
      fun _ segment => segment.rawKind? != some `Lean.Parser.Command.macroTail
    inheritBase :=
      fun _ segment => segment.rawKind? != some `Lean.Parser.Command.macroTail
    breakPoints := notationBreaks
  }

def macroRule : LineBreakRule :=
  {
    name := "macro"
    useExistingBreaks := fun _ _ => true
    breakPoints :=
      fun _ segment =>
        match firstChildRawKind? segment `Lean.Parser.Command.macroTail with
        | some index => [boundaryBreak? segment index 1].filterMap id
        | none => []
  }

def configEntriesRule : LineBreakRule :=
  {
    name := "configEntries"
    mandatory := fun _ segment => (breakAfterLexeme? segment "where" 1).isSome
    inheritBase := fun _ _ => true
    breakPoints :=
      fun _ segment => [breakAfterLexeme? segment "where" 1].filterMap id
  }

def configCommandRule : LineBreakRule :=
  {
    name := "configCommand"
    inheritBase := fun _ _ => true
    breakPoints := leadingAnnotationBreaks
  }

def letRecDeclarationRule : LineBreakRule :=
  {
    name := "letRecDeclaration"
    inheritBase := fun _ _ => true
    breakPoints :=
      fun context segment =>
        let indentLevels :=
          if context.ancestors.any
              fun frame =>
                frame.rawKind? == some `Lean.Parser.Term.letRecDecls then
            1
          else
            0
        terminationSuffixChildBreaksWithIndent segment indentLevels
  }

def letRecEquationRule : LineBreakRule :=
  {
    name := "letRecEquation"
    mandatory := fun _ _ => true
    inheritBase := fun _ _ => true
    breakPoints := letRecEquationBreaks
  }

def moduleRule : LineBreakRule :=
  {
    name := "module"
    mandatory :=
      fun context segment =>
        !(moduleHeaderBreaks context segment).isEmpty
        || !(moduleBodyBreaks context segment).isEmpty
    breakPoints :=
      fun context segment =>
        moduleHeaderBreaks context segment ++ moduleBodyBreaks context segment
  }

def setOptionRule : LineBreakRule :=
  {
    name := "setOption"
    mandatory := fun context segment => !(setOptionBreaks context segment).isEmpty
    useExistingBreaks := fun _ _ => true
    breakPoints := setOptionBreaks
  }

def transparentRule : LineBreakRule :=
  {
    name := "transparent"
    formatOriginalChildLeadingBoundary :=
      fun _ segment index =>
        segment.indexes.any
          fun childIndex =>
            childIndex < index && (segment.child? childIndex).any treeHasContent
  }

def suffixGroupRule : LineBreakRule :=
  {
    name := "suffixGroup"
    inheritBase := fun _ _ => true
  }

def namedDiscriminantRule : LineBreakRule :=
  {
    name := "namedDiscriminant"
    useExistingBreaks := fun _ _ => true
    flow := fun _ _ => true
    breakPoints := fun _ segment => [boundaryBreak? segment 1 0].filterMap id
  }

def dotIdentRule : LineBreakRule :=
  {
    name := "dotIdent"
    atomic := true
  }

def interpolatedStringRule : LineBreakRule :=
  {
    name := "interpolatedString"
    atomic := true
  }

def parenRule : LineBreakRule :=
  {
    name := "paren"
    flow := fun context segment => !(patternAliasParenBreaks context segment).isEmpty
    inheritBase :=
      fun context _ => parentIsRawKind context `Lean.Parser.Term.namedPattern
    breakPoints := patternAliasParenBreaks
  }

/-! ### Infix and control-flow rule values -/

def mutualRule : LineBreakRule :=
  {
    name := "mutual"
    mandatory := fun _ _ => true
    breakPoints := mutualBreaks
  }

def infixChainRule : LineBreakRule :=
  {
    name := "infixChain"
    useExistingBreaks := fun _ segment => lowPriorityInfixAllRhsCanFlow segment
    flow := infixFlow
    keepPrefixWithChildFirstLine :=
      fun _ segment index => childLowPriorityInfixRhsHasAttachedBody segment index
    inheritBase := infixAttachedBodyAssignmentValue
    liftsTailIndentation :=
      fun context segment =>
        !infixAttachedBodyAssignmentValue context segment
        && !(infixRuleBreaks context segment).isEmpty
    breakPoints := infixRuleBreaks
  }

def lowPriorityInfixRhsRule : LineBreakRule :=
  {
    name := "lowPriorityInfixRhs"
    mandatory := fun _ segment => lowPriorityInfixRhsHasMandatoryAlignedBody segment
    flow := fun _ _ => true
    inheritBase := fun _ _ => true
    keepPrefixWithChildFirstLine :=
      fun _ segment index =>
        index == segment.start + 1 && !lowPriorityInfixRhsHasMandatoryAlignedBody segment
    breakPoints := lowPriorityInfixRhsBreaks
  }

def binderTacticRule : LineBreakRule :=
  {
    name := "binderTactic"
    inheritBase := fun _ _ => true
    breakPoints := binderTacticBreaks
  }

def bigOperatorRule : LineBreakRule :=
  {
    name := "bigOperator"
    breakPoints := bigOperatorBreaks
  }

def binderPredicateRule : LineBreakRule :=
  {
    name := "binderPredicate"
    inheritBase := fun _ _ => true
    breakPoints := defaultChildBreaks
  }

def commandInChainRule : LineBreakRule :=
  {
    name := "commandInChain"
    mandatory := fun context segment => !(commandInBreaks context segment).isEmpty
    useExistingBreaks := fun _ _ => true
    breakPoints := commandInBreaks
  }

def tacticLayoutOwnerRule : LineBreakRule :=
  {
    name := "tacticLayoutOwner"
    mandatory :=
      fun context segment => !(tacticLayoutOwnerBreaks context segment).isEmpty
    flow := fun _ _ => true
    inheritBase := fun _ _ => true
    roundUpBaseIndentation := true
    breakPoints := tacticLayoutOwnerBreaks
  }

def tacticEliminationHeaderRule : LineBreakRule :=
  {
    name := "tacticEliminationHeader"
    keepPrefixWithChildFirstLine :=
      fun _ segment index =>
        (segment.child? index).any
          fun
          | .node .tacticIdentifierClause _ => true
          | _ => false
    flow := fun _ _ => true
    inheritBase := fun _ _ => true
    breakPoints := tacticEliminationHeaderBreaks
  }

def tacticAlternativeContainerRule : LineBreakRule :=
  {
    name := "tacticAlternativeContainer"
    useExistingBreaks := fun _ _ => true
    flow := fun _ _ => true
    inheritBase := fun _ _ => true
    roundUpBaseIndentation := true
    breakPoints := tacticAlternativeContainerBreaks
  }

def tacticAlternativeRule : LineBreakRule :=
  {
    name := "tacticAlternative"
    useExistingBreaks := fun _ _ => true
    flow := fun _ _ => true
    inheritBase := fun _ _ => true
    roundUpBaseIndentation := true
    breakPoints := tacticAlternativeBodyBreaks
  }

def tacticIdentifierClauseRule : LineBreakRule :=
  {
    name := "tacticIdentifierClause"
    useExistingBreaks := fun _ _ => true
    flow := fun _ _ => true
    inheritBase := fun _ _ => true
    breakPoints := tacticIdentifierClauseBreaks
  }

def ifThenElseRule : LineBreakRule :=
  {
    name := "ifThenElse"
    useExistingBreaks := fun _ _ => true
    startAlignment := fun _ _ => .preferred
    roundUpBaseIndentation := true
    breakPoints := ifThenElseBreaks
  }

def dependentIfThenElseRule : LineBreakRule :=
  {
    name := "dependentIfThenElse"
    useExistingBreaks := fun _ _ => true
    startAlignment := fun _ _ => .preferred
    roundUpBaseIndentation := true
    breakPoints := dependentIfThenElseBreaks
  }

def ifLetThenElseRule : LineBreakRule :=
  {
    name := "ifLetThenElse"
    useExistingBreaks := fun _ _ => true
    startAlignment := fun _ _ => .preferred
    roundUpBaseIndentation := true
    breakPoints := ifLetThenElseBreaks
  }

def ifThenElseChainRule : LineBreakRule :=
  {
    name := "ifThenElseChain"
    useExistingBreaks := fun _ _ => true
    startAlignment := fun _ _ => .preferred
    roundUpBaseIndentation := true
    breakPoints := ifThenElseChainBreaks
  }

def matchExpressionRule : LineBreakRule :=
  {
    name := "matchExpression"
    mandatory := fun _ _ => true
    breakPoints := matchExpressionBreaks
  }

def quantifierRule : LineBreakRule :=
  {
    name := "quantifier"
    breakPoints := quantifierBreaks
  }

def basicFunRule : LineBreakRule :=
  {
    name := "basicFun"
    useExistingBreaks := fun _ _ => true
    inheritBase :=
      fun _ segment =>
        match segment.parent with
        | .node .patternLambda _ => false
        | _ => true
    breakPoints := basicFunBreaks
  }

def prefixedTermRule (name : String) : LineBreakRule :=
  {
    name
    inheritBase := fun _ _ => true
  }

def unaryPrefixRule : LineBreakRule :=
  prefixedTermRule "unaryPrefix"

def nestedActionRule : LineBreakRule :=
  prefixedTermRule "nestedAction"

def unsafeTermRule : LineBreakRule :=
  prefixedTermRule "unsafeTerm"

def matchPatternsRule : LineBreakRule :=
  {
    name := "matchPatterns"
    useExistingBreaks := fun _ _ => true
    inheritBase := fun _ _ => true
    breakPoints := matchPatternBreaks
  }

def matchDiscriminantsRule : LineBreakRule :=
  {
    name := "matchDiscriminants"
    useExistingBreaks := fun _ _ => true
    flow := fun _ _ => true
    inheritBase := fun context _ => matchDiscriminantsFollowMotive context
    breakPoints := matchDiscriminantBreaks
  }

def subtypeRule : LineBreakRule :=
  {
    name := "subtype"
    breakPoints := subtypeBreaks
  }

def matchAltRule : LineBreakRule :=
  {
    name := "matchAlt"
    useExistingBreaks := fun _ _ => true
    flow := fun _ _ => true
    breakPoints := matchAltBreaks
  }

def matchExprAltRule : LineBreakRule :=
  {
    name := "matchExprAlt"
    mandatory := fun _ _ => true
    inheritBase := fun _ _ => true
    breakPoints := matchExprAltBreaks
  }

def doRule : LineBreakRule :=
  {
    name := "do"
    mandatory := fun _ _ => true
    inheritBase := fun _ _ => true
    breakPoints := doBreaks
  }

def doTryRule : LineBreakRule :=
  {
    name := "doTry"
    mandatory := fun _ _ => true
    inheritBase := fun _ _ => true
    breakPoints := doTryBreaks
  }

def doCatchRule : LineBreakRule :=
  {
    name := "doCatch"
    mandatory := fun _ _ => true
    inheritBase := fun _ _ => true
    breakPoints := doCatchBreaks
  }

def doForRule : LineBreakRule :=
  {
    name := "doFor"
    mandatory := fun _ _ => true
    inheritBase := fun _ _ => true
    breakPoints := doForBreaks
  }

def doFinallyRule : LineBreakRule :=
  {
    name := "doFinally"
    inheritBase := fun _ _ => true
    breakPoints := doFinallyBreaks
  }

def doForHeaderRule : LineBreakRule :=
  {
    name := "doForHeader"
    inheritBase := fun _ _ => true
    liftsTailIndentation := fun _ _ => true
    breakPoints := doForHeaderBreaks
  }

def doUnlessRule : LineBreakRule :=
  {
    name := "doUnless"
    mandatory := fun _ _ => true
    inheritBase := fun _ _ => true
    breakPoints := doUnlessBreaks
  }

def fromTermRule : LineBreakRule :=
  {
    name := "fromTerm"
    inheritBase := fun _ _ => true
    breakPoints := fromTermBreaks
  }

def sufficesRule : LineBreakRule :=
  {
    name := "suffices"
    mandatory := fun _ _ => true
    inheritBase := fun _ _ => true
    breakPoints := sufficesBreaks
  }

def haveRule : LineBreakRule :=
  {
    name := "have"
    mandatory := fun _ _ => true
    startAlignment := fun _ _ => .required
    inheritBase :=
      fun context _ =>
        !parentIsInfixChain context && !parentIsRawKind context `Lean.Parser.Term.typeSpec
    breakPoints := haveBreaks
  }

def doIfRule : LineBreakRule :=
  {
    name := "doIf"
    mandatory := fun _ _ => true
    inheritBase := fun _ _ => true
    breakPoints := doIfBreaks
  }

def extendedBinderTypeGroup (context : RuleContext) : Bool :=
  match context.ancestors with
  | parent :: grandparent :: _ =>
      parent.rawKind? == some `null
      && grandparent.rawKind? == some `Batteries.ExtendedBinder.extBinder
      && grandparent.childIndex == 1
  | _ => false

def groupBreaks (context : RuleContext) (segment : Segment) : List BreakPoint :=
  if extendedBinderTypeGroup context then
    []
  else
    let elseIfBreaks := doElseIfBreaks context segment
    if elseIfBreaks.isEmpty then defaultBreaks context segment else elseIfBreaks

def groupRule : LineBreakRule :=
  {
    name := "group"
    useExistingBreaks :=
      fun context segment =>
        (doElseIfBreaks context segment).isEmpty && !(groupBreaks context segment).isEmpty
    mandatory := fun context segment => !(doElseIfBreaks context segment).isEmpty
    flow :=
      fun context segment =>
        (doElseIfBreaks context segment).isEmpty
        && !(groupBreaks context segment).isEmpty
        && !defaultIsInfix context segment
    liftsTailIndentation :=
      fun context segment =>
        (doElseIfBreaks context segment).isEmpty
        && !(groupBreaks context segment).isEmpty
        && defaultIsInfix context segment
    breakPoints := groupBreaks
  }

def lakeDslWrapperRule : LineBreakRule :=
  {
    name := "lakeDslWrapper"
    inheritBase := fun _ _ => true
  }

def lakeCommandBreaks (context : RuleContext) (segment : Segment) : List BreakPoint :=
  let annotationBreaks := leadingAnnotationBreaks context segment
  let configBreaks := [breakAfterLexeme? segment "where" 1].filterMap id
  annotationBreaks ++ configBreaks

def lakeCommandHasConfigBody (segment : Segment) : Bool :=
  (breakAfterLexeme? segment "where" 1).isSome

def lakeCommandRule : LineBreakRule :=
  {
    name := "lakeCommand"
    useExistingBreaks := fun _ _ => true
    mandatory := fun _ segment => lakeCommandHasConfigBody segment
    flow := fun _ segment => !lakeCommandHasConfigBody segment
    inheritBase := fun _ _ => true
    breakPoints := lakeCommandBreaks
  }

def lakeRequireBreaks (_context : RuleContext) (segment : Segment) : List BreakPoint :=
  [breakAfterLexeme? segment "git" 1].filterMap id

def lakeRequireRule : LineBreakRule :=
  {
    name := "lakeRequire"
    useExistingBreaks := fun _ _ => true
    inheritBase := fun _ _ => true
    breakPoints := lakeRequireBreaks
  }

def lakeFromGitBreaks (_context : RuleContext) (segment : Segment) : List BreakPoint :=
  [boundaryBreak? segment 1 1].filterMap id

def lakeFromGitRule : LineBreakRule :=
  {
    name := "lakeFromGit"
    useExistingBreaks := fun _ _ => true
    inheritBase := fun _ _ => true
    breakPoints := lakeFromGitBreaks
  }

def registerLinterSetBreaks (_context : RuleContext) (segment : Segment)
    : List BreakPoint :=
  match contentIndexAfterLexeme? segment ":=" with
  | some firstLinterIndex =>
      segment.indexes.filterMap
        fun index =>
          if firstLinterIndex <= index then
            boundaryBreak? segment index 1
          else
            none
  | none => []

def registerLinterSetRule : LineBreakRule :=
  {
    name := "registerLinterSet"
    mandatory := fun context segment => !(registerLinterSetBreaks context segment).isEmpty
    breakPoints := registerLinterSetBreaks
  }

def matchAltsWhereDeclsRule : LineBreakRule :=
  {
    name := "matchAltsWhereDecls"
    mandatory := fun _ _ => true
    breakPoints := matchAltsWhereDeclsBreaks
  }

def matchAltsRule : LineBreakRule :=
  {
    name := "matchAlts"
    mandatory := fun _ _ => true
    inheritBase :=
      fun context _ => !parentIsRawKind context `Lean.Parser.Term.letEqnsDecl
    breakPoints := matchAltsBreaks
  }

-----------------------------------------------------------------------------------------
-- Rule dispatch
-----------------------------------------------------------------------------------------

def isGeneratedMathlibCrossRefKind (kind : Lean.SyntaxNodeKind) : Bool :=
  let name := toString kind
  [
    ".Mathlib.CrossRef.wikidataTag",
    ".Mathlib.CrossRef.stacksTag",
    ".Mathlib.CrossRef.stacksTagDBStacks",
    ".Mathlib.CrossRef.stacksTagDBKerodon",
    ".Mathlib.CrossRef.lmfdbTag"
  ].any
    fun suffix => name.endsWith suffix

partial def ruleFor : SyntaxTree.Tree → Option LineBreakRule
  | .missing => some defaultRule
  | .leaf _ => some defaultRule
  | .node (.tactic kind _ _ _) children => ruleFor (.node (.raw kind) children)
  -- Module and declaration wrappers with generic layout.
  | .node (.raw `null) _ => some nullRule
  | .node (.raw `Lean.Parser.Module.module) _ => some moduleRule
  | .node (.raw `Lean.Parser.Module.header) _ => some moduleRule
  | .node (.raw `Lean.Parser.Module.import) _ => some moduleRule
  | .node (.raw `Lean.Parser.Module.all) _ => some defaultRule
  | .node (.raw `Lean.Parser.Module.moduleTk) _ => some defaultRule
  | .node (.raw `Lean.Parser.Module.public) _ => some defaultRule
  | .node (.raw `Lean.Parser.Module.meta) _ => some defaultRule
  | .node (.raw `Lean.Parser.Command.moduleDoc) _ => some defaultRule
  | .node (.raw `Lean.Parser.Command.docComment) _ => some defaultRule
  | .node (.raw `Lean.Parser.Command.sectionHeader) _ => some defaultRule
  | .node (.raw `Lean.Parser.Command.namespace) _ => some defaultRule
  | .node (.raw `Lean.Parser.Command.end) _ => some defaultRule
  | .node (.raw `Lean.Parser.Command.open) _ => some transparentRule
  | .node (.raw `Lean.Parser.Command.openSimple) _ => some defaultRule
  | .node (.raw `Lean.Parser.Command.openScoped) _ => some defaultRule
  | .node (.raw `Lean.Parser.Command.openOnly) _ => some defaultRule
  | .node (.raw `Lean.Parser.Command.variable) _ => some variableCommandRule
  | .node (.raw `Lean.Parser.Command.set_option) _ => some setOptionRule
  | .node (.raw `Lean.Parser.Command.declModifiers) _ =>
      some declarationModifierRule
  | .node (.raw `Lean.Parser.Command.declId) _ => some declarationIdentifierRule
  | .node (.raw `Lean.Parser.Command.declValEqns) _ => some defaultRule
  | .node .derivingClause _ => some derivingClauseRule
  | .node .unifConstraints _ => some unifConstraintsRule
  | .node (.raw `Lean.Parser.Command.optDeriving) _ => some defaultRule
  | .node (.raw `Lean.Parser.Command.deriving) _ => some defaultRule
  | .node (.raw `Lean.Parser.Command.derivingClass) _ => some defaultRule
  | .node (.raw `Lean.Parser.Command.structureTk) _ => some defaultRule
  | .node (.raw `Lean.Parser.Command.classTk) _ => some defaultRule
  | .node (.raw `Lean.Parser.Command.private) _ => some defaultRule
  | .node (.raw `Lean.Parser.Command.public) _ => some defaultRule
  | .node (.raw `Lean.Parser.Command.meta) _ => some defaultRule
  | .node (.raw `Lean.Parser.Command.unsafe) _ => some defaultRule
  | .node (.raw `Lean.Parser.Command.opaque) _ => some defaultRule
  | .node (.raw `Lean.Parser.Command.noncomputable) _ => some defaultRule
  | .node (.raw `Lean.Parser.Command.protected) _ => some defaultRule
  | .node (.raw `Lean.Parser.Command.partial) _ => some defaultRule
  | .node (.raw `Lean.Parser.Command.eval) _ => some defaultRule
  | .node (.raw `Lean.Parser.Command.check) _ => some defaultRule
  | .node (.raw `Lean.Parser.Command.example) _ => some defaultRule
  | .node (.raw `Lean.Parser.Command.universe) _ => some defaultRule
  | .node (.raw `Lean.Parser.Command.syntax) _ => some defaultRule
  | .node (.raw `Lean.Parser.Command.syntaxCat) _ => some defaultRule
  | .node (.raw `Lean.Parser.Command.binderPredicate) _ => some defaultRule
  | .node (.raw `Lean.Parser.Command.macro) _ => some macroRule
  | .node (.raw `Lean.Parser.Command.macro_rules) _ => some defaultRule
  | .node (.raw `Lean.Parser.Command.elab) _ => some transparentRule
  | .node (.raw `Lean.Parser.Command.elabTail) _ => some transparentRule
  | .node (.raw `Lean.Parser.Command.elab_rules) _ => some defaultRule
  | .node (.raw `Lean.Parser.Command.initialize) _ => some defaultRule
  | .node (.raw `Lean.Parser.Command.section) _ => some defaultRule
  | .node (.raw `Lean.Parser.Command.initializeKeyword) _ => some defaultRule
  | .node (.raw `Lean.runCmd) _ => some transparentRule
  | .node (.raw `Lean.includeStr) _ => some defaultRule
  | .node (.raw `Lean.Option.registerOption) _ => some declarationValueRule
  | .node (.raw `Lean.Parser.Command.namedName) _ => some defaultRule
  | .node (.raw `Lean.Parser.Command.macroArg) _ => some defaultRule
  | .node (.raw `Lean.Parser.Command.macroTail) _ => some notationRule
  | .node (.raw `Lean.Parser.Command.macroRhs) _ => some defaultRule
  | .node (.raw `Lean.Parser.Command.attribute) _ => some commandAttributeRule
  | .node (.raw `Mathlib.Linter.UnusedTactic.«command#allow_unused_tactic!___») _ =>
      some defaultRule
  | .node (.raw `Lean.Parser.Command.deprecated_module) _ => some defaultRule
  | .node (.raw `Lean.Parser.Command.assertNotImported) _ => some defaultRule
  | .node (.raw `Lean.Parser.Command.assertNotExists) _ => some assertNotExistsRule
  | .node (.raw `Lean.Parser.Command.namedPrio) _ => some defaultRule
  | .node (.raw `Lean.Parser.Command.abbrev) _ => some defaultRule
  | .node (.raw `Lean.Parser.Command.classAbbrev) _ => some defaultRule
  | .node (.raw `Lean.Parser.Command.nonrec) _ => some defaultRule
  | .node (.raw `Lean.Parser.Command.notation) _ => some notationRule
  | .node (.raw `Lean.Parser.Command.mixfix) _ => some notationRule
  | .node (.raw `Lean.Parser.Command.infix) _ => some notationRule
  | .node (.raw `Lean.Parser.Command.infixl) _ => some notationRule
  | .node (.raw `Lean.Parser.Command.infixr) _ => some notationRule
  | .node (.raw `Lean.Parser.Command.prefix) _ => some notationRule
  | .node (.raw `Lean.Parser.Command.postfix) _ => some notationRule
  | .node (.raw `Lean.Parser.Command.identPrec) _ => some defaultRule
  | .node (.raw `Lean.Parser.Command.grindPattern) _ => some defaultRule
  | .node (.raw `Lean.Parser.Command.omit) _ => some defaultRule
  | .node (.raw `Lean.Parser.Command.include) _ => some defaultRule
  | .node (.raw `Lean.Parser.Command.structParent) _ => some defaultRule
  | .node (.raw `Lean.Parser.Command.structCtor) _ => some structCtorRule
  | .node (.raw `Lean.Parser.Command.structInstBinder) _ => some defaultRule
  | .node (.raw `Lean.Parser.Command.structImplicitBinder) _ =>
      some defaultRule
  | .node (.raw `Lean.Parser.Command.structExplicitBinder) _ =>
      some transparentRule
  | .node (.raw `Lean.Parser.Command.extends) _ => some transparentRule
  | .node (.raw `Lean.Parser.Command.initialize_simps_projections) _ => some defaultRule
  | .node (.raw `Lean.Parser.Command.simpsProj) _ => some defaultRule
  | .node (.raw `Lean.Parser.Command.simpsRule) _ => some defaultRule
  | .node (.raw `Lean.Parser.Command.simpsRule.add) _ => some unaryPrefixRule
  | .node (.raw `Lean.Parser.Command.simpsRule.prefix) _ => some defaultRule
  | .node (.raw `Lean.Parser.Command.simpsRule.erase) _ => some unaryPrefixRule
  | .node (.raw `Lean.Parser.Command.eraseAttr) _ => some defaultRule
  | .node (.raw `Lean.Parser.Command.classInductive) _ => some defaultRule
  | .node (.raw `Lean.Parser.commandUnseal__) _ => some defaultRule
  | .node (.raw `Lean.Parser.Command.recommended_spelling) _ => some defaultRule
  | .node (.raw `Lean.guardMsgsCmd) _ => some commandInChainRule
  | .node (.raw `Topology.nhdsGT) _ => some transparentRule
  | .node (.raw `Topology.nhdsLT) _ => some transparentRule
  | .node (.raw `Topology.nhdsNE) _ => some transparentRule
  | .node (.raw `Topology.nhdsLE) _ => some transparentRule
  | .node (.raw `Topology.nhdsGE) _ => some transparentRule
  | .node (.raw `Topology.IsOpen_of) _ => some defaultRule
  | .node (.raw `Topology.IsClosed_of) _ => some defaultRule
  | .node (.raw `Topology.closure_of) _ => some defaultRule
  | .node (.raw `Topology.Continuous_of) _ => some defaultRule
  | .node (.raw `Lean.«command__Unif_hint____Where_|_-⊢__») _ =>
      some defaultRule
  | .node (.raw `Lean.unifConstraintElem) _ => some defaultRule
  | .node (.raw `Lake.DSL.packageCommand) _ => some lakeCommandRule
  | .node (.raw `Lake.DSL.leanLibCommand) _ => some lakeCommandRule
  | .node (.raw `Lake.DSL.requireDecl) _ => some lakeRequireRule
  | .node (.raw `Lake.DSL.identOrStr) _ => some lakeDslWrapperRule
  | .node (.raw `Lake.DSL.optConfig) _ => some lakeDslWrapperRule
  | .node (.raw `Lake.DSL.declValWhere) _ => some whereStructInstRule
  | .node (.raw `Lake.DSL.depSpec) _ => some lakeDslWrapperRule
  | .node (.raw `Lake.DSL.depName) _ => some lakeDslWrapperRule
  | .node (.raw `Lake.DSL.fromClause) _ => some lakeDslWrapperRule
  | .node (.raw `Lake.DSL.fromSource) _ => some lakeDslWrapperRule
  | .node (.raw `Lake.DSL.fromGit) _ => some lakeFromGitRule
  | .node (.raw `Lean.Linter.«command_Register_linter_set_:=_») _ =>
      some registerLinterSetRule
  | .node (.raw `lemma) _ => some theoremRule
  -- Transparent expression wrappers and atomic syntax.
  | .node (.raw `Lean.Parser.Term.paren) _ => some parenRule
  | .node (.raw `Lean.Parser.Term.fun) _ => some transparentRule
  | .node (.raw `Lean.Parser.Term.nestedAction) _ => some nestedActionRule
  | .node (.raw `Lean.Parser.Term.unsafe) _ => some unsafeTermRule
  | .node (.raw `Lean.Parser.Term.typeSpec) _ => some transparentRule
  | .node (.raw `Lean.Parser.Command.declValSimple) _ =>
      some declarationValueRule
  | .node (.raw `Lean.Parser.Command.instance) _ => some instanceRule
  | .node (.raw `Lean.Parser.Command.ctor) _ => some transparentRule
  | .node (.raw `Lean.Parser.Command.structSimpleBinder) _ => some transparentRule
  | .node (.raw `Lean.Parser.Term.structInstField) _ => some structInstFieldRule
  | .node (.raw `Lean.Parser.Term.structInstFieldDef) _ => some transparentRule
  | .node (.raw `Lean.Parser.Term.structInstFieldEqns) _ =>
      some transparentRule
  | .node (.raw `Lean.Parser.Term.structInstLVal) _ => some transparentRule
  | .node (.raw `Lean.Parser.Term.namedPattern) _ => some transparentRule
  | .node (.raw `Lean.Parser.Term.pipeProj) _ => some pipeProjRule
  | .node (.raw `Lean.Parser.Term.hygienicLParen) _ => some defaultRule
  | .node (.raw `hygieneInfo) _ => some defaultRule
  | .node (.raw `Lean.Parser.Term.type) _ => some defaultRule
  | .node (.raw `Lean.Parser.Term.prop) _ => some defaultRule
  | .node (.raw `Lean.Parser.Term.motive) _ => some transparentRule
  | .node (.raw `Lean.Parser.Term.leading_parser) _ => some applicationRule
  | .node (.raw `Lean.Parser.Term.typeAscription) _ => some typeAscriptionRule
  | .node (.raw `Lean.Parser.Term.optEllipsis) _ => some defaultRule
  | .node (.raw `Lean.Parser.Term.explicit) _ => some <| prefixedTermRule "explicit"
  | .node (.raw `Lean.Parser.Term.explicitUniv) _ =>
      some <| prefixedTermRule "explicitUniv"
  | .node (.raw `Lean.Parser.Term.have) _ => some haveRule
  | .node (.raw `Lean.Parser.Term.haveI) _ => some haveRule
  | .node (.raw `Lean.Parser.Term.hole) _ => some defaultRule
  | .node (.raw `Lean.Parser.Term.syntheticHole) _ => some defaultRule
  | .node (.raw `Lean.Parser.Term.suffices) _ => some sufficesRule
  | .node (.raw `Lean.Parser.Term.sufficesDecl) _ => some defaultRule
  | .node (.raw `Lean.Parser.Term.open) _ => some commandInChainRule
  | .node (.raw `Lean.Parser.Term.termReturn) _ =>
      some <| prefixedTermRule "termReturn"
  | .node (.raw `Lean.Parser.Term.panic) _ => some defaultRule
  | .node (.raw `Lean.Parser.Term.sorry) _ => some defaultRule
  | .node (.raw `Lean.Parser.Term.stateRefT) _ => some defaultRule
  | .node (.raw `Lean.Parser.Term.unreachable) _ => some defaultRule
  | .node (.raw `Lean.Parser.Term.typeOf) _ => some defaultRule
  | .node (.raw `Lean.Parser.Term.dynamicQuot) _ => some defaultRule
  | .node (.raw `Lean.Parser.Term.sort) _ => some defaultRule
  | .node (.raw `Lean.Parser.Term.letConfig) _ => some defaultRule
  | .node (.raw `Lean.Parser.Term.letDecl) _ => some defaultRule
  | .node (.raw `Lean.Parser.Term.letI) _ => some letRule
  | .node (.raw `Lean.Parser.Term.letPosOpt) _ => some defaultRule
  | .node (.raw `Lean.Parser.Term.letOpts) _ => some defaultRule
  | .node (.raw `Lean.Parser.Term.letOptNondep) _ => some defaultRule
  | .node (.raw `Lean.Parser.Term.doLetExpr) _ => some doLetExprRule
  | .node (.raw `Lean.Parser.Term.doIfLetBind) _ => some doIfLetBindRule
  | .node (.raw `Lean.Parser.Term.doHave) _ => some defaultRule
  | .node (.raw `Lean.Parser.Term.inferInstanceAs) _ => some defaultRule
  | .node (.raw `Lean.Parser.Term.noindex) _ => some defaultRule
  | .node (.raw `Lean.Parser.Term.configItem) _ => some defaultRule
  | .node (.raw `Lean.Parser.Term.negConfigItem) _ => some defaultRule
  | .node (.raw `Lean.Parser.Term.letRecDecls) _ => some letRecDeclarationRule
  | .node (.raw `Lean.Parser.Term.letRecDecl) _ => some letRecDeclarationRule
  | .node (.raw `Lean.Parser.Term.letEqnsDecl) _ => some letRecEquationRule
  | .node (.raw `Lean.Parser.Term.letId) _ => some defaultRule
  | .node (.raw `Lean.Parser.Term.letIdDeclNoBinders) _ => some letIdDeclRule
  | .node (.raw `Lean.Parser.Term.matchDiscr) _ => some transparentRule
  | .node (.raw `Lean.Parser.Term.doMatchExpr) _ => some matchExpressionRule
  | .node (.raw `Lean.Parser.Term.doAssert) _ => some defaultRule
  | .node (.raw `Lean.Parser.Term.matchExprAlts) _ => some matchAltsRule
  | .node (.raw `Lean.Parser.Term.matchExprAlt) _ => some matchExprAltRule
  | .node (.raw `Lean.Parser.Term.matchExprElseAlt) _ => some matchExprAltRule
  | .node (.raw `Lean.Parser.Term.matchExprPat) _ => some defaultRule
  | .node (.raw `Lean.Parser.Term.binderDefault) _ => some binderDefaultRule
  | .node (.raw `Lean.Parser.Term.namedArgument) _ => some namedArgumentRule
  | .node (.raw `Lean.Parser.Term.strictImplicitBinder) _ => some defaultRule
  | .node (.raw `Lean.Parser.Term.anonymousCtor) _ => some anonymousCtorRule
  | .node (.raw `Lean.Parser.Term.local) _ => some defaultRule
  | .node (.raw `Lean.Parser.Term.instBinder) _ => some transparentRule
  | .node (.raw `Lean.Parser.Term.attrKind) _ => some defaultRule
  | .node (.raw `Lean.Parser.Term.attrInstance) _ => some defaultRule
  | .node (.raw `Lean.Parser.Term.attributes) _ => some defaultRule
  | .node (.raw `Lean.Parser.Term.scoped) _ => some defaultRule
  | .node (.raw `Lean.Parser.Term.ellipsis) _ => some defaultRule
  | .node (.raw `Lean.Parser.Term.nomatch) _ => some defaultRule
  | .node (.raw `Lean.Parser.Term.nofun) _ => some defaultRule
  | .node (.raw `Lean.Parser.Term.quotedName) _ => some defaultRule
  | .node (.raw `Lean.Parser.Term.withAnonymousAntiquot) _ => some defaultRule
  | .node (.raw `Lean.Parser.Term.falseVal) _ => some defaultRule
  | .node (.raw `Lean.Parser.Term.cdot) _ => some defaultRule
  | .node (.raw `Lean.Parser.Term.show) _ => some transparentRule
  | .node (.raw `Lean.Parser.Term.fromTerm) _ => some fromTermRule
  | .node (.raw `Lean.Parser.Term.byTactic) _ => some byTacticRule
  | .node (.raw `Lean.Parser.Term.byTactic') _ => some byTacticRule
  | .node (.raw `Lean.Parser.Termination.suffix) _ => some terminationSuffixRule
  | .node (.raw `Lean.Parser.Termination.terminationBy) _ => some terminationByRule
  | .node (.raw `Lean.Parser.Termination.terminationBy?) _ => some defaultRule
  | .node (.raw `Lean.Parser.Termination.decreasingBy) _ => some decreasingByRule
  | .node (.raw `Lean.Parser.Termination.partialFixpoint) _ => some defaultRule
  | .node (.raw `Lean.Parser.Termination.coinductiveFixpoint) _ => some defaultRule
  | .node (.raw `Lean.Parser.Termination.inductiveFixpoint) _ => some defaultRule
  | .node (.raw `Lean.Parser.Term.whereFinally) _ => some whereFinallyRule
  | .node (.proofBody _) _ => some defaultRule
  | .node (.raw `Lean.Parser.Tactic.tacticSeq) _ => some defaultRule
  | .node (.raw `Lean.Parser.Tactic.tacticSeq1Indented) _ => some defaultRule
  | .node (.raw `Lean.Parser.Tactic.tacticRwa__) _ => some defaultRule
  | .node (.raw `Lean.Parser.Tactic.rwRuleSeq) _ => some defaultRule
  | .node (.raw `Lean.Parser.Tactic.rwRule) _ => some defaultRule
  | .node (.raw `Lean.Parser.Tactic.location) _ => some defaultRule
  | .node (.raw `Lean.Parser.Tactic.locationHyp) _ => some defaultRule
  | .node (.raw `Lean.Parser.Tactic.exact) _ => some defaultRule
  | .node (.raw `Lean.Parser.Tactic.cases) _ => some tacticLayoutOwnerRule
  | .node (.raw `Lean.Parser.Tactic.induction) _ => some tacticLayoutOwnerRule
  | .node (.tacticEliminationTargets _) _ => some matchDiscriminantsRule
  | .node (.tacticEliminationHeader _) _ => some tacticEliminationHeaderRule
  | .node .tacticIdentifierClause _ => some tacticIdentifierClauseRule
  | .node (.raw `Lean.Parser.Tactic.inductionAlts) _ =>
      some tacticAlternativeContainerRule
  | .node (.raw `Lean.Parser.Tactic.inductionAlt) _ => some tacticAlternativeRule
  | .node (.raw `Lean.Parser.Tactic.tacticRfl) _ => some defaultRule
  | .node (.raw `Lean.Parser.Tactic.grind) _ => some defaultRule
  | .node (.raw `Lean.Parser.Tactic.optConfig) _ => some defaultRule
  | .node (.raw `Lean.Parser.Tactic.posConfigItem) _ => some defaultRule
  | .node (.raw `Lean.Parser.Tactic.negConfigItem) _ => some defaultRule
  | .node (.raw `Lean.Parser.Tactic.valConfigItem) _ => some defaultRule
  | .node (.raw `Lean.Parser.Term.doNested) _ => some doRule
  | .node (.raw `Lean.Parser.Term.doSeqBracketed) _ => some defaultRule
  -- Known leaf-like parser nodes handled by generic spacing and layout.
  | .node (.raw `Lean.binderIdent) _ => some defaultRule
  | .node (.raw `Lean.explicitBinders) _ => some defaultRule
  | .node (.raw `Lean.unbracketedExplicitBinders) _ => some defaultRule
  | .node (.raw `Lean.bracketedExplicitBinders) _ => some defaultRule
  | .node (.raw `num) _ => some defaultRule
  | .node (.raw `scientific) _ => some defaultRule
  | .node (.raw `str) _ => some defaultRule
  | .node (.raw `name) _ => some defaultRule
  | .node (.raw `Lean.Parser.Term.declName) _ => some defaultRule
  | .node (.raw `char) _ => some defaultRule
  | .node (.raw `fieldIdx) _ => some defaultRule
  | .node (.raw `patternIgnore) _ => some defaultRule
  | .node (.raw `termℕ) _ => some defaultRule
  | .node (.raw `termℤ) _ => some defaultRule
  | .node (.raw `termℚ) _ => some defaultRule
  | .node (.raw `termℝ) _ => some defaultRule
  | .node (.raw `rawNatLit) _ => some defaultRule
  | .node (.raw `Nat.term_!) _ => some defaultRule
  | .node (.raw `Lean.Elab.Term.«termType*») _ => some defaultRule
  | .node (.raw `Lean.Elab.Term.«termSort*») _ => some defaultRule
  | .node (.raw `coeNotation) _ => some defaultRule
  | .node (.raw `coeSortNotation) _ => some defaultRule
  | .node (.raw `Lean.calc) _ => some defaultRule
  | .node (.raw `Lean.calcSteps) _ => some defaultRule
  | .node (.raw `Lean.calcFirstStep) _ => some defaultRule
  | .node (.raw `Lean.modCast) _ => some defaultRule
  | .node (.raw `Lean.«term∀__,_») _ => some quantifierRule
  | .node (.raw `Lean.«term∃__,_») _ => some quantifierRule
  | .node (.raw `Lean.«binderPred∈_») _ => some binderPredicateRule
  | .node (.raw `Lean.«binderPred<_») _ => some binderPredicateRule
  | .node (.raw `Lean.«binderPred>_») _ => some binderPredicateRule
  | .node (.raw `Lean.«binderPred≤_») _ => some binderPredicateRule
  | .node (.raw `Lean.«binderPred≥_») _ => some binderPredicateRule
  | .node (.raw `Lean.«binderPred≠_») _ => some binderPredicateRule
  | .node (.raw `Lean.«binderPred∉_») _ => some binderPredicateRule
  | .node (.raw `Mathlib.Meta.SetNotationForOrder.«binderPred⊆_») _ =>
      some defaultRule
  | .node (.raw `Mathlib.Meta.SetNotationForOrder.«binderPred⊂_») _ =>
      some defaultRule
  | .node (.raw `Mathlib.Meta.SetNotationForOrder.«binderPred⊇_») _ =>
      some defaultRule
  | .node (.raw `termDepIfThenElse) _ => some dependentIfThenElseRule
  | .node (.raw `termIfLet) _ => some ifLetThenElseRule
  | .node (.raw `BigOperators.bigsum) _ => some bigOperatorRule
  | .node (.raw `BigOperators.bigprod) _ => some bigOperatorRule
  | .node (.raw `BigOperators.bigexpect) _ => some bigOperatorRule
  | .node (.raw `BigOperators.bigOpBinders) _ => some defaultRule
  | .node (.raw `BigOperators.bigOpBinder) _ => some transparentRule
  | .node (.raw `BigOperators.bigOpBinderCollection) _ => some defaultRule
  | .node (.raw `BigOperators.bigOpBinderParenthesized) _ => some defaultRule
  | .node (.raw `ArithmeticFunction.bigproddvd) _ => some defaultRule
  | .node (.raw `Algebra.subalgebra_adjoin) _ => some defaultRule
  | .node (.raw `Std.termF!_) _ => some defaultRule
  | .node (.raw `Batteries.ExtendedBinder.extBinders) _ => some defaultRule
  | .node (.raw `Batteries.ExtendedBinder.extBinder) _ => some binderRule
  | .node (.raw `Batteries.ExtendedBinder.extBinderCollection) _ => some defaultRule
  | .node (.raw `Batteries.ExtendedBinder.extBinderParenthesized) _ =>
      some binderRule
  | .node (.raw `choice) _ => some transparentRule
  | .node (.raw `Lean.Parser.Syntax.atom) _ => some transparentRule
  | .node (.raw `Lean.Parser.Syntax.unary) _ => some defaultRule
  | .node (.raw `Lean.Parser.Syntax.cat) _ => some transparentRule
  | .node (.raw `Lean.Parser.Syntax.paren) _ => some transparentRule
  | .node (.raw `Lean.Parser.Syntax.nonReserved) _ => some defaultRule
  | .node (.raw `stx_?) _ => some transparentRule
  | .node (.raw `«stx_,*») _ => some transparentRule
  | .node (.raw `Lean.Parser.Term.quot) _ => some defaultRule
  | .node (.raw `Lean.Parser.Tactic.quot) _ => some defaultRule
  | .node (.raw `term!_) _ => some unaryPrefixRule
  | .node (.raw `«term¬_») _ => some unaryPrefixRule
  | .node (.raw `token.«← ») _ => some defaultRule
  | .node (.raw `Lean.Parser.Attr.simp) _ => some defaultRule
  | .node (.raw `Lean.Parser.Attr.grind) _ => some defaultRule
  | .node (.raw `Lean.Parser.Attr.grind!) _ => some defaultRule
  | .node (.raw `Lean.Parser.Attr.grindMod) _ => some defaultRule
  | .node (.raw `Lean.Parser.Attr.grindEq) _ => some defaultRule
  | .node (.raw `Lean.Parser.Attr.grindEqBoth) _ => some defaultRule
  | .node (.raw `Lean.Parser.Attr.grindDef) _ => some defaultRule
  | .node (.raw `Lean.Parser.Attr.grindLR) _ => some defaultRule
  | .node (.raw `Lean.Parser.Attr.grindFwd) _ => some defaultRule
  | .node (.raw `Lean.Parser.Attr.grindBwd) _ => some defaultRule
  | .node (.raw `Lean.Parser.Attr.grindCases) _ => some defaultRule
  | .node (.raw `Lean.Parser.Attr.simple) _ => some defaultRule
  | .node (.raw `Lean.Parser.Attr.simps) _ => some defaultRule
  | .node (.raw `Lean.Parser.Attr.attrSimps!_) _ => some defaultRule
  | .node (.raw `Lean.Parser.Attr.simpsArgsRest) _ => some defaultRule
  | .node (.raw `Lean.Parser.Attr.simpsConfig) _ => some defaultRule
  | .node (.raw `Lean.Parser.Attr.simpsConfigItem) _ => some defaultRule
  | .node (.raw `Lean.Parser.Attr.norm_cast) _ => some defaultRule
  | .node (.raw `Lean.Parser.Attr.ext) _ => some defaultRule
  | .node (.raw `Lean.Parser.Attr.extIff) _ => some defaultRule
  | .node (.raw `Lean.Parser.Attr.higherOrder) _ => some defaultRule
  | .node (.raw `Lean.Attr.coe) _ => some defaultRule
  | .node (.raw `Lean.Parser.Attr.instance) _ => some defaultRule
  | .node (.raw `Lean.Parser.Attr.class) _ => some defaultRule
  | .node (.raw `Lean.deprecated) _ => some defaultRule
  | .node (.raw `token.existing) _ => some defaultRule
  | .node (.raw `Parser.Attr.functor_norm) _ => some defaultRule
  | .node (.raw `Parser.Attr.fin_omega) _ => some defaultRule
  | .node (.raw `Parser.Attr.enat_to_nat_top) _ => some defaultRule
  | .node (.raw `Parser.Attr.enat_to_nat_coe) _ => some defaultRule
  | .node (.raw `Parser.Attr.pnat_to_nat_coe) _ => some defaultRule
  | .node (.raw `Parser.Attr.zify_simps) _ => some defaultRule
  | .node (.raw `Lean.Parser.Attr.simpsConfigAttrItem) _ => some defaultRule
  | .node (.raw `attrContinuity) _ => some defaultRule
  | .node (.raw `Mathlib.Tactic.ToAdditive.to_additive) _ => some defaultRule
  | .node (.raw `Lean.Elab.Command.irredDefLemma) _ => some defaultRule
  | .node (.raw `Lean.Elab.Command.aux_def) _ => some defaultRule
  | .node (.raw `Mathlib.Tactic.MkIff.mkIff) _ => some defaultRule
  | .node (.raw `Mathlib.Tactic.Translate.attrArgs) _ => some defaultRule
  | .node (.raw `ArithmeticFunction.attrArith_mult) _ => some defaultRule
  | .node (.raw `Parser.Attr.coassoc_simps) _ => some defaultRule
  | .node (.raw `Parser.Attr.ghost_simps) _ => some defaultRule
  | .node (.raw `Mathlib.Tactic.Translate.bracketedOption) _ => some defaultRule
  | .node (.raw `Mathlib.Tactic.Translate.translationHint) _ => some defaultRule
  | .node (.raw `«term{}») _ => some defaultRule
  | .node (.raw `Lean.Parser.Level.hole) _ => some defaultRule
  | .node (.raw `Lean.Parser.Level.paren) _ => some defaultRule
  | .node (.raw `Lean.Parser.Level.max) _ => some defaultRule
  | .node (.raw `«term∅») _ => some defaultRule
  | .node (.raw `«term⊤») _ => some defaultRule
  | .node (.raw `«term⊥») _ => some defaultRule
  | .node (.raw `«term-_») _ => some unaryPrefixRule
  | .node (.raw `«term~~~_») _ => some unaryPrefixRule
  | .node (.raw `«term_⁻¹») _ => some defaultRule
  | .node (.raw `«term_ˣ») _ => some defaultRule
  | .node (.raw `«term_ᵐᵒᵖ») _ => some defaultRule
  | .node (.raw `«term__[_]») _ => some indexedTermRule
  | .node (.raw `Uniformity.«term𝓤[_]») _ => some transparentRule
  | .node (.raw `Asymptotics.«term_=O[_]_») _ => some bracketedRelationRule
  | .node (.raw `Asymptotics.«term_=o[_]_») _ => some bracketedRelationRule
  | .node (.raw `Asymptotics.«term_=Θ[_]_») _ => some bracketedRelationRule
  | .node (.raw `«term_→ₗ[_]_») _ => some defaultRule
  | .node (.raw `«term_≃ₗ[_]_») _ => some defaultRule
  | .node (.raw `«term_→ₐ[_]_») _ => some defaultRule
  | .node (.raw `«term_≡_[MOD_]») _ => some defaultRule
  | .node (.raw `«term_≡_[ZMOD_]») _ => some defaultRule
  | .node (.raw `PiNotation.piNotation) _ => some defaultRule
  | .node (.raw `coeFunNotation) _ => some defaultRule
  | .node (.raw `Mathlib.Meta.setBuilder) _ => some setBuilderRule
  | .node (.raw `Set.Mathlib.Meta.setBuilder) _ => some setBuilderRule
  | .node (.raw `Mathlib.Meta.«term{_|_}») _ => some setBuilderRule
  | .node (.raw `Mathlib.Meta.«term{_|_}_1») _ => some setBuilderRule
  | .node
      (.raw
        `Ideal.Submodule.Module.Submodule.Module.Module.Submodule.Submodule.Module.Module.Submodule.Submodule.QuotientTorsion.Ideal.Quotient.AddMonoid.AddSubgroup.torsionByStx)
      _ => some defaultRule
  | .node (.raw `Mathlib.Meta.macroPattSetBuilder) _ => some setBuilderRule
  | .node (.raw `Mathlib.Notation3.notation3) _ => some notationRule
  | .node (.raw `Mathlib.Notation3.notation3Item) _ => some defaultRule
  | .node (.raw `Mathlib.Notation3.identOptScoped) _ => some defaultRule
  | .node (.raw `Mathlib.Notation3.prettyPrintOpt) _ => some defaultRule
  | .node (.raw `Mathlib.Notation3.foldAction) _ => some defaultRule
  | .node (.raw `Mathlib.Notation3.foldKind) _ => some defaultRule
  | .node (.raw `LinearAlgebra.Projectivization.termℙ) _ => some defaultRule
  | .node (.raw `Qq.matcher) _ => some defaultRule
  | .node (.raw `Qq.doElemAssertInstancesCommute) _ => some defaultRule
  | .node (.raw `Lean.«doElemTrace[_]__») _ => some defaultRule
  | .node (.raw `term.pseudo.antiquot) _ => some defaultRule
  | .node (.raw `Lean.termThrowError__) _ => some defaultRule
  | .node (.raw `Mathlib.Elab.FastInstance.fastInstance) _ => some defaultRule
  | .node (.raw `Mathlib.ProxyType.proxy_equiv) _ =>
      some <| prefixedTermRule "proxyEquiv"
  | .node (.raw `Mathlib.Tactic.scopedNS) _ => some defaultRule
  | .node (.raw `Mathlib.Tactic.Push.pushAttr) _ => some defaultRule
  | .node (.raw `Mathlib.Tactic.GCongr.gcongrAttr) _ => some defaultRule
  | .node (.raw `Mathlib.Tactic.Monotonicity.Attr.mono) _ => some defaultRule
  | .node (.raw `Mathlib.CrossRef.wikidataTag) _ => some defaultRule
  | .node (.raw `Mathlib.CrossRef.stacksTag) _ => some defaultRule
  | .node (.raw `Mathlib.CrossRef.stacksTagDBStacks) _ => some defaultRule
  | .node (.raw `Mathlib.CrossRef.stacksTagDBKerodon) _ => some defaultRule
  | .node (.raw `Mathlib.CrossRef.lmfdbTag) _ => some defaultRule
  | .node (.raw `stacksTag) _ => some defaultRule
  | .node (.raw `Parser.Attr.parity_simps) _ => some defaultRule
  | .node (.raw `Parser.Attr.nontriviality) _ => some defaultRule
  | .node (.raw `Parser.Attr.mfld_simps) _ => some defaultRule
  | .node (.raw `Parser.Attr.rclike_simps) _ => some defaultRule
  | .node (.raw `Parser.Attr.mon_tauto) _ => some defaultRule
  | .node (.raw `Batteries.Tactic.Alias.alias) _ => some defaultRule
  | .node (.raw `Batteries.Tactic.Alias.aliasLR) _ => some defaultRule
  | .node (.raw `Batteries.Tactic.Lint.nolint) _ => some defaultRule
  | .node (.raw `Batteries.Util.LibraryNote.commandLibrary_note___) _ =>
      some defaultRule
  | .node (.raw `Finsupp.Internal.stxSingle₀) _ => some defaultRule
  | .node (.raw `Finsupp.Internal.stxUpdate₀) _ => some defaultRule
  | .node (.raw `Finsupp.fun₀) _ => some defaultRule
  | .node (.raw `Finsupp.fun₀.matchAlts) _ => some defaultRule
  | .node (.raw `Mathlib.Util.TermReduce.deltaStx) _ => some defaultRule
  | .node (.raw `Aesop.Frontend.Parser.aesop) _ => some defaultRule
  | .node (.raw `Aesop.Frontend.Parser.aesopTactic) _ => some defaultRule
  | .node (.raw `Aesop.Frontend.Parser.bool_litTrue) _ => some defaultRule
  | .node (.raw `Aesop.Frontend.Parser.bool_litFalse) _ => some defaultRule
  | .node (.raw `Aesop.Frontend.Parser.declareRuleSets) _ =>
      some defaultRule
  | .node (.raw `Aesop.Frontend.Parser.attr_rules_) _ => some defaultRule
  | .node (.raw `Aesop.Frontend.Parser.rule_expr_) _ => some defaultRule
  | .node (.raw `Aesop.Frontend.Parser.rule_expr___) _ =>
      some recursiveSequenceRule
  | .node (.raw `Aesop.Frontend.Parser.ruleSetsFeature) _ => some defaultRule
  | .node (.raw `Aesop.Frontend.Parser.feature_) _ => some defaultRule
  | .node (.raw `Aesop.Frontend.Parser.feature__1) _ => some defaultRule
  | .node (.raw `Aesop.Frontend.Parser.feature__2) _ => some defaultRule
  | .node (.raw `Aesop.Frontend.Parser.feature__3) _ => some defaultRule
  | .node (.raw `Aesop.Frontend.Parser.feature__4) _ => some defaultRule
  | .node (.raw `Aesop.Frontend.Parser.«feature(_)») _ => some defaultRule
  | .node (.raw `Aesop.Frontend.Parser.phaseSafe) _ => some defaultRule
  | .node (.raw `Aesop.Frontend.Parser.phaseNorm) _ => some defaultRule
  | .node (.raw `Aesop.Frontend.Parser.phaseUnsafe) _ => some defaultRule
  | .node (.raw `Aesop.Frontend.Parser.builder_nameApply) _ => some defaultRule
  | .node (.raw `Aesop.Frontend.Parser.builder_nameCases) _ => some defaultRule
  | .node (.raw `Aesop.Frontend.Parser.builder_nameDestruct) _ =>
      some defaultRule
  | .node (.raw `Aesop.Frontend.Parser.builder_nameForward) _ => some defaultRule
  | .node (.raw `Aesop.Frontend.Parser.builder_nameTactic) _ => some defaultRule
  | .node (.raw `Aesop.Frontend.Parser.builder_nameUnfold) _ => some defaultRule
  | .node (.raw `Aesop.Frontend.Parser.«builder_option(Index:=[_])») _ =>
      some defaultRule
  | .node (.raw `Aesop.Frontend.Parser.indexing_modeTarget_) _ => some defaultRule
  | .node (.raw `Aesop.Frontend.Parser.«priority_%») _ => some defaultRule
  | .node (.raw `Aesop.Frontend.Parser.«priority-_») _ => some defaultRule
  | .node (.raw `measurability) _ => some defaultRule
  | .node (.raw `finiteness) _ => some defaultRule
  | .node (.raw `eqns) _ => some defaultRule
  | .node (.raw `positivity) _ => some defaultRule
  | .node (.raw `Mathlib.Meta.Positivity.Meta.Positivity.Tactic.Positivity.positivity) _
    => some defaultRule
  | .node (.raw `norm_num) _ => some defaultRule
  | .node (.raw `prioLow) _ => some defaultRule
  | .node (.raw `prioMid) _ => some defaultRule
  | .node (.raw `prioHigh) _ => some defaultRule
  | .node (.raw `prioDefault) _ => some defaultRule
  | .node (.raw `Lean.Parser.precedence) _ => some defaultRule
  | .node (.raw `precArg) _ => some defaultRule
  | .node (.raw `precMax) _ => some defaultRule
  | .node (.raw `cfcTac) _ => some defaultRule
  | .node (.raw `adaptationNoteCmd) _ => some defaultRule
  | .node (.raw `Lean.Parser.discrTreeSimpKeyCmd) _ => some defaultRule
  | .node (.raw `Lean.Elab.ConfigEval.defEvalConfigItemCmd) _ =>
      some configCommandRule
  | .node (.raw `Lean.Elab.ConfigEval.declareCoreConfigElab) _ =>
      some configCommandRule
  | .node (.raw `Lean.Elab.ConfigEval.declareTermConfigElab) _ =>
      some configCommandRule
  | .node (.raw `Lean.Elab.ConfigEval.declareTacticConfig) _ =>
      some configCommandRule
  | .node (.raw `Lean.Elab.ConfigEval.declareCommandConfig) _ =>
      some configCommandRule
  | .node (.raw `Lean.Elab.ConfigEval.deriveEvalExprUsingMeta) _ =>
      some defaultRule
  | .node (.raw `Lean.Elab.ConfigEval.configEntries) _ => some configEntriesRule
  | .node (.raw `Lean.Elab.ConfigEval.configEntry) _ => some defaultRule
  | .node (.raw `Lean.Elab.ConfigEval.configEntryOmit) _ => some defaultRule
  | .node (.raw `Lean.Elab.ConfigEval.configEntryHandler) _ =>
      some declarationValueRule
  | .node (.raw `Lean.Elab.ConfigEval.configEntryHandlerKey) _ =>
      some defaultRule
  | .node (.raw `Lean.Elab.ConfigEval.configEntryHandlerKeyPrefix) _ =>
      some defaultRule
  | .node (.raw `adaptationNoteTermStx) _ => some defaultRule
  | .node (.raw `commandSuppress_compilation) _ => some defaultRule
  | .node (.raw `notation_class) _ => some defaultRule
  | .node (.raw `wikidataId) _ => some defaultRule
  | .node (.raw `goldenRatio.termφ) _ => some defaultRule
  | .node (.raw `goldenRatio.termψ) _ => some defaultRule
  | .node (.raw `Topology.term𝓝) _ => some defaultRule
  | .node (.raw `FinsetFamily.term𝓒) _ => some defaultRule
  | .node (.raw `FinsetFamily.term𝓓) _ => some defaultRule
  | .node (.raw `Cardinal.termℵ₀) _ => some defaultRule
  | .node (.raw `Matroid.aesop_mat) _ => some defaultRule
  | .node (.raw `Matroid.ExchangeProperty.aesop_mat) _ => some defaultRule
  | .node (.raw `aesop_graph) _ => some defaultRule
  | .node (.raw `Aesop.Frontend.Parser.addRules) _ => some defaultRule
  | .node (.raw `CategoryTheory.cat_disch) _ => some defaultRule
  | .node (.raw `CategoryTheory.SimplicialObject.Truncated.mkNotation) _ =>
      some defaultRule
  | .node (.raw `SimplexCategory.Truncated.mkNotation) _ => some defaultRule
  | .node (.raw `TopCat.Presheaf.attrSheaf_restrict) _ => some defaultRule
  | .node (.raw `TopCat.Presheaf.attrSheaf_restrict_1) _ => some defaultRule
  | .node (.raw `aliasIn) _ => some defaultRule
  | .node (.raw `Mathlib.Tactic.TermCongr.termCongr) _ => some defaultRule
  | .node (.raw `Mathlib.Tactic.dsimpPercent) _ => some defaultRule
  | .node (.raw `Mathlib.Meta.FunProp.funPropTacStx) _ => some defaultRule
  | .node (.raw `Lean.Parser.Command.registerTryTactic) _ => some defaultRule
  | .node (.raw `Mathlib.PPWithUniv.ppWithUnivAttr) _ => some defaultRule
  | .node (.raw `Mathlib.Util.«commandCompile_inductive%_») _ =>
      some defaultRule
  | .node (.raw `Mathlib.Util.«commandCompile_def%_») _ => some defaultRule
  | .node (.raw `Mathlib.GuardExceptions.parseCmd) _ => some defaultRule
  | .node (.raw `transImportsStx) _ => some defaultRule
  | .node (.raw `commandUnsuppress_compilationIn_) _ => some commandInChainRule
  | .node (.raw `proof_wanted) _ => some defaultRule
  | .node (.raw `antiquotNestedExpr) _ => some defaultRule
  | .node (.raw `Lean.Parser.«command__Dsimproc__[_]_(_):=_») _ =>
      some defaultRule
  | .node (.raw `Lean.Parser.«command_Dsimproc_decl_(_):=_») _ =>
      some defaultRule
  | .node (.raw `«term{_}») _ => some bracedTermRule
  | .node (.raw `«term[_]») _ => some arrayRule
  | .node (.raw `«term#[_,]») _ => some arrayRule
  | .node (.raw `Matrix.vecNotation) _ => some arrayRule
  | .node (.raw `Matrix.matrixNotation) _ => some matrixNotationRule
  | .node (.raw `PiLp.vecNotation) _ => some transparentRule
  | .node (.raw `«term__[_]_?») _ => some transparentRule
  -- Syntax with specialized formatting rules.
  | .node (.raw `Lean.Parser.Command.declaration) _ => some declarationRule
  | .node .annotatedDeclaration _ => some annotatedDeclarationRule
  | .node (.raw `Lean.Parser.Command.structure) _ => some structureRule
  | .node .structureHeader _ => some structureHeaderRule
  | .node .structureConstructor _ => some structureConstructorRule
  | .node .structureDeriving _ => some structureDerivingRule
  | .node (.raw `Lean.Parser.Command.export) _ => some exportRule
  | .node .definition _ => some definitionRule
  | .node (.raw `Lean.Parser.Command.definition) _ => some rawDefinitionRule
  | .node (.raw `Lean.Parser.Command.theorem) _ => some theoremRule
  | .node (.raw `Lean.Parser.Term.structInst) _ => some structInstRule
  | .node (.raw `Lean.Parser.Term.tuple) _ => some tupleRule
  | .node (.raw `Lean.Parser.Term.structInstFields) _ => some structInstFieldsRule
  | .node (.raw `Lean.Parser.Command.structFields) _ => some structFieldsRule
  | .node (.raw `Lean.Parser.Command.inductive) _ => some inductiveRule
  | .node (.raw `Lean.Parser.Command.coinductive) _ => some inductiveRule
  | .node .application _ => some applicationRule
  | .node (.indexedInfix _) _ => some indexedNotationRule
  | .node .patternLambda _ => some basicFunRule
  | .node .signatureParameters _ => some signatureParametersRule
  | .node .matchPatterns _ => some matchPatternsRule
  | .node .matchDiscriminants _ => some matchDiscriminantsRule
  | .node .doForHeader _ => some doForHeaderRule
  | .node .doFallbackClause _ => some doFallbackClauseRule
  | .node .doFallbackContinuation _ => some doFallbackContinuationRule
  | .node .structureUpdate _ => some structureUpdateRule
  | .node (.raw `Lean.Parser.Command.optDeclSig) _ => some signatureRule
  | .node (.raw `Lean.Parser.Command.declSig) _ => some signatureRule
  | .node (.raw `Lean.Parser.Term.explicitBinder) _ => some binderRule
  | .node (.raw `Lean.Parser.Term.implicitBinder) _ => some binderRule
  | .node (.raw `Lean.Parser.Term.let) _ => some letRule
  | .node (.letExpression kind _) _ =>
      if kind == `Lean.Parser.Term.letrec then some letRecRule else some letRule
  | .node (.raw `Lean.Parser.Term.letrec) _ => some letRecRule
  | .node (.raw `Lean.Parser.Term.letIdDecl) _ => some letIdDeclRule
  | .node (.raw `Lean.Parser.Term.letPatDecl) _ => some letPatternDeclRule
  | .node (.raw `Lean.Parser.Term.whereDecls) _ => some whereDeclsRule
  | .node .suffixGroup _ => some suffixGroupRule
  | .node .namedDiscriminant _ => some namedDiscriminantRule
  | .node (.raw `Lean.Parser.Command.whereStructInst) _ => some whereStructInstRule
  | .node (.raw `Lean.Parser.Command.mutual) _ => some mutualRule
  | .node (.infixChain `Lean.Parser.Command.in) _ => some commandInChainRule
  | .node (.infixChain `Lean.Parser.Term.binderTactic) _ =>
      some binderTacticRule
  | .node .lowPriorityInfixRhs _ => some lowPriorityInfixRhsRule
  | .node (.infixChain _) _ => some infixChainRule
  | .node .ifThenElseClause _ => some transparentRule
  | .node .ifThenElseChain _ => some ifThenElseChainRule
  | .node (.raw `termIfThenElse) _ => some ifThenElseRule
  | .node (.raw `boolIfThenElse) _ => some ifThenElseRule
  | .node (.raw `Lean.Parser.Term.match) _ => some matchExpressionRule
  | .node (.raw `Lean.Parser.Term.forall) _ => some quantifierRule
  | .node (.raw `Lean.Parser.Term.exists) _ => some quantifierRule
  | .node (.raw `«term∃_,_») _ => some quantifierRule
  | .node (.raw `Lean.Parser.Term.basicFun) _ => some basicFunRule
  | .node (.raw `«term{_:_//_}») _ => some subtypeRule
  | .node (.raw `Lean.Parser.Term.matchAlt) _ => some matchAltRule
  | .node (.raw `Lean.Parser.Term.do) _ => some doRule
  | .node (.raw `Lean.Parser.Term.doRepeat) _ => some doRule
  | .node (.raw `Lean.Parser.Term.doBreak) _ => some defaultRule
  | .node (.raw `Lean.Parser.Term.doDbgTrace) _ => some defaultRule
  | .node (.raw `Lean.Parser.Term.doIdbg) _ => some defaultRule
  | .node (.raw `Lean.Parser.Term.doLet) _ => some doLetRule
  | .node (.raw `Lean.Parser.Term.doLetRec) _ => some doLetRecRule
  | .node (.raw `Lean.Parser.Term.doLetElse) _ => some doLetElseRule
  | .node (.raw `Lean.Parser.Term.doMatch) _ => some matchExpressionRule
  | .node (.raw `Lean.Parser.Term.doTry) _ => some doTryRule
  | .node (.raw `Lean.Parser.Term.doCatch) _ => some doCatchRule
  | .node (.raw `Lean.Parser.Term.doCatchMatch) _ => some doRule
  | .node (.raw `Lean.Parser.Term.doFor) _ => some doForRule
  | .node (.raw `Lean.Parser.Term.doWhile) _ => some doForRule
  | .node (.raw `Lean.Parser.Term.doFinally) _ => some doFinallyRule
  | .node (.raw `Lean.Parser.Term.doContinue) _ => some defaultRule
  | .node (.raw `Lean.Parser.Term.doIf) _ => some doIfRule
  | .node (.raw `Lean.Parser.Term.doReassign) _ => some transparentRule
  | .node (.raw `Lean.Parser.Term.doReassignArrow) _ => some transparentRule
  | .node (.raw `Lean.Parser.Term.doReturn) _ =>
      some <| prefixedTermRule "doReturn"
  | .node (.raw `Lean.Parser.Term.doIfProp) _ => some transparentRule
  | .node (.raw `Lean.Parser.Term.doUnless) _ => some doUnlessRule
  | .node (.raw `Lean.Parser.Term.doForDecl) _ => some transparentRule
  | .node (.raw `Lean.Parser.Term.liftMethod) _ => some transparentRule
  | .node (.raw `Lean.Parser.Term.dotIdent) _ => some dotIdentRule
  | .node (.raw `termS!_) _ => some interpolatedStringRule
  | .node (.raw `Lean.termM!_) _ => some interpolatedStringRule
  | .node (.raw `interpolatedStrKind) _ => some interpolatedStringRule
  | .node (.raw `interpolatedStrLitKind) _ => some interpolatedStringRule
  | .node (.raw `Lean.Parser.Term.doSeqIndent) _ => some doSeqIndentRule
  | .node (.raw `Lean.Parser.Term.doSeqItem) _ => some defaultRule
  | .node (.raw `Lean.Parser.Term.doExpr) _ => some defaultRule
  | .node (.raw `Lean.Parser.Term.doIfLet) _ => some transparentRule
  | .node (.raw `Lean.Parser.Term.doIfLetPure) _ => some declarationValueRule
  | .node (.raw `Lean.Parser.Term.doLetArrow) _ => some doLetRule
  | .node (.raw `Lean.Parser.Term.doIdDecl) _ => some doIdDeclRule
  | .node (.raw `Lean.Parser.Term.doPatDecl) _ => some doPatternDeclRule
  | .node (.raw `Lean.Parser.Term.dbgTrace) _ => some dbgTraceRule
  | .node (.raw `Lean.Parser.Term.idbg) _ => some dbgTraceRule
  | tree@(.node (.raw `group) _) =>
      if treeFirstLexeme? tree == some "lemma" then some theoremRule else some groupRule
  | .node (.raw `Lean.Parser.Term.matchAltsWhereDecls) _ => some matchAltsWhereDeclsRule
  | .node (.raw `Lean.Parser.Term.matchAlts) _ => some matchAltsRule
  | .node (.raw kind) children =>
      if isGeneratedIndexedPrefixTerm kind children then
        some indexedTermRule
      else if isSymmetricDelimitedGeneratedTerm kind children
              || isGeneratedPostfixTerm kind children then
        some transparentRule
      else if children.back?.any
                fun child =>
                  match child with
                  | .node (.raw childKind) _ => childKind == kind
                  | _ => false then
        some recursiveSequenceRule
      else if treeIsBinderOperatorTerm (.node (.raw kind) children) then
        some quantifierRule
      else if SyntaxTree.isCoreTacticKindName (SyntaxTree.nodeKindName (.raw kind)) then
        some defaultRule
      else if isGeneratedLocalNotationKind kind
              || isGeneratedMathlibCrossRefKind kind then
        some defaultRule
      else
        none

partial def treeStartsWithProjectionChain : SyntaxTree.Tree → Bool
  | .node (.infixChain `Lean.Parser.Term.proj) _ => true
  | .node .application children =>
      children[0]?.any treeStartsWithProjectionChain
  | .node (.raw kind) children =>
      (kind == `Lean.Parser.Term.paren
        || kind == `Lean.Parser.Term.hygienicLParen
        || kind == `null)
      && children.any treeStartsWithProjectionChain
  | _ => false

def treeIsUnbreakableHead (tree : SyntaxTree.Tree) : Bool :=
  tree.singleToken?.isSome
  || treeStartsWithProjectionChain tree
  || (ruleFor tree).any (·.atomic)

partial def treeStartsWithSourceBrokenUnbreakableHead (source : String)
    : SyntaxTree.Tree → Bool
  | .node .application children =>
      match children[0]?, children[1]? with
      | some head, some firstArgument =>
          treeIsUnbreakableHead head
          && match head.lastToken?, firstArgument.firstToken? with
              | some left, some right =>
                  SpaceRules.hasLineStructure
                    (SyntaxTree.sourceText source left.span.stop right.span.start)
              | _, _ => false
      | _, _ => false
  | .node (.raw kind) children =>
      (kind == `Lean.Parser.Term.paren
        || kind == `Lean.Parser.Term.hygienicLParen
        || kind == `null)
      && children.any (treeStartsWithSourceBrokenUnbreakableHead source)
  | _ => false

def treeHasUnbreakableFirstLine
    (source : String) (tree : SyntaxTree.Tree) (rule : LineBreakRule)
    : Bool :=
  tree.singleToken?.isSome
  || rule.atomic
  || treeStartsWithProjectionChain tree
  || treeStartsWithSourceBrokenUnbreakableHead source tree

def formattingRuleFor (tree : SyntaxTree.Tree) : LineBreakRule :=
  match ruleFor tree with
  | some rule => rule
  | none => defaultRule

end LineBreakRules
end Formatter
end LeanFmt
