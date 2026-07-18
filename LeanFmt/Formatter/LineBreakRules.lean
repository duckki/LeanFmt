import LeanFmt.SyntaxTree

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
  (List.range segment.size).map fun offset => segment.start + offset

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
  | _ => none

def RuleContext.push (context : RuleContext) (segment : Segment) (childIndex : Nat)
    : RuleContext :=
  { ancestors := { segment, childIndex } :: context.ancestors }

def RuleContext.parentRawKind? (context : RuleContext) : Option Lean.SyntaxNodeKind :=
  match context.ancestors.head? with
  | some frame =>
      match frame.segment.parent with
      | .node (.raw kind) _ => some kind
      | _ => none
  | none => none

def Frame.rawKind? (frame : Frame) : Option Lean.SyntaxNodeKind :=
  match frame.segment.parent with
  | .node (.raw kind) _ => some kind
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
      && grandparent.rawKind? == some `«term[_]»
      && grandparent.childIndex == 1
  | _ => false

def RuleContext.parentIsStructureWhereWrapper (context : RuleContext) : Bool :=
  match context.ancestors with
  | parent :: _ =>
      parent.rawKind? == some `Lean.Parser.Command.structure && parent.childIndex == 4
  | _ => false

def defaultInheritBase (context : RuleContext) (segment : Segment) : Bool :=
  context.parentIsSingletonArrayItemWrapper
  || segment.rawKind? == some `Lean.Parser.Term.letDecl
  || (segment.rawKind? == some `null && context.parentIsStructureWhereWrapper)

def parentIsSignatureParameters (context : RuleContext) : Bool :=
  match context.ancestors with
  | parent :: _ => parent.nodeKind? == some .signatureParameters
  | _ => false

def parentIsRawKind (context : RuleContext) (kind : Lean.SyntaxNodeKind) : Bool :=
  context.parentRawKind? == some kind

def grandparentIsRawKind (context : RuleContext) (kind : Lean.SyntaxNodeKind) : Bool :=
  match context.ancestors with
  | _ :: grandparent :: _ => grandparent.rawKind? == some kind
  | _ => false

structure LineBreakRule where
  name : String
  atomic : Bool := false
  useExistingBreaks : RuleContext → Segment → Bool := fun _ _ => false
  mandatory : RuleContext → Segment → Bool := fun _ _ => false
  flow : RuleContext → Segment → Bool := fun _ _ => false
  inheritBase : RuleContext → Segment → Bool := defaultInheritBase
  accumulatesInfixLeftDepth : RuleContext → Segment → Bool := fun _ _ => false
  alignStartToIndentation : RuleContext → Segment → Bool := fun _ _ => false
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
  | _ => false

def firstChildRawKind? (segment : Segment) (kind : Lean.SyntaxNodeKind) : Option Nat :=
  segment.indexes.find? fun index => childIsRawKind segment index kind

def treeHasContent : SyntaxTree.Tree → Bool
  | .missing => false
  | .leaf token => !token.lexeme.isEmpty
  | .node _ children => !children.isEmpty

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

def childStartsWithLexeme (segment : Segment) (index : Nat) (lexeme : String) : Bool :=
  match segment.child? index with
  | some child => treeFirstLexeme? child == some lexeme
  | none => false

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
  lexemeIn lexeme ["by", "do", "where", "with", "deriving", "then", "else"]

def suffixDelimiterLexeme (lexeme : String) : Bool :=
  lexemeIn lexeme [")", "]", "}", "⟩", "⟫", ",", ";"]

def suffixOperatorLexeme (lexeme : String) : Bool :=
  lexemeIn lexeme
    [
      ":=",
      "=>",
      ":",
      "|",
      "=",
      "==",
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

def suffixProjectionMember (context : RuleContext) : Bool :=
  match context.ancestors with
  | parent :: _ =>
      parent.nodeKind? == some (.infixChain `Lean.Parser.Term.proj)
      && parent.childIndex != 0
  | _ => false

def suffixTokenAction (context : RuleContext) (token : SyntaxTree.Token)
    : SuffixTokenAction :=
  if token.lexeme.isEmpty then
    .skip
  else if suffixProjectionMember context then
    .emit
  else if suffixEligibleToken token then
    .emit
  else
    .stop

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
    accumulatesInfixLeftDepth := defaultIsInfix
    breakPoints := defaultBreaks
  }

-----------------------------------------------------------------------------------------
-- Custom Rules
-----------------------------------------------------------------------------------------

/-! ### Shared wrapper and context rules -/

def singletonArrayItemWrapper (context : RuleContext) (segment : Segment) : Bool :=
  parentIsRawKind context `«term[_]» && segmentContentCount segment == 1

def rawKindIsQuantifier (kind : Lean.SyntaxNodeKind) : Bool :=
  kind == `Lean.Parser.Term.forall
  || kind == `Lean.Parser.Term.exists
  || kind == `«term∃_,_»

def quantifierBinderSequence (context : RuleContext) : Bool :=
  match context.ancestors with
  | parent :: _ =>
      match parent.rawKind? with
      | some kind => rawKindIsQuantifier kind && parent.childIndex == 1
      | none => false
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

def exportIdentifierList (context : RuleContext) : Bool :=
  match context.ancestors with
  | parent :: _ =>
      parent.rawKind? == some `Lean.Parser.Command.export && parent.childIndex == 3
  | _ => false

def nullInheritBase (context : RuleContext) (segment : Segment) : Bool :=
  defaultInheritBase context segment
  || singletonArrayItemWrapper context segment
  || quantifierBinderSequence context
  || parentIsRawKind context `Lean.Parser.Term.structInstFields
  || parentIsRawKind context `Lean.Parser.Term.letRecDecls
  || parentIsRawKind context `Lean.Parser.Term.letRecDecl

def attachedBodyStart (segment : Segment) (index : Nat) : Bool :=
  childStartsWithLexeme segment index "do" || childStartsWithLexeme segment index "by"

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

def treeContainsAttachedBodyStart (tree : SyntaxTree.Tree) : Bool :=
  treeContainsLexeme "by" tree || treeContainsLexeme "do" tree

def declarationValueBreakWithoutNestedBody? (segment : Segment)
    : Option BreakPoint := do
  let valueIndex ← contentIndexAfterLexeme? segment ":="
  let value ← segment.child? valueIndex
  if attachedBodyStart segment valueIndex || treeContainsAttachedBodyStart value then
    none
  else
    boundaryBreak? segment valueIndex 1

def declarationValueBreaksWithoutNestedBody (_context : RuleContext) (segment : Segment)
    : List BreakPoint :=
  [declarationValueBreakWithoutNestedBody? segment].filterMap id

/-! ### Declarations, structures, and collections -/

def definitionBreaks (_context : RuleContext) (segment : Segment) : List BreakPoint :=
  let valueBreak := [declarationValueBreak? segment].filterMap id
  let whereBreak :=
    match segment.indexes.find?
            fun index => childStartsWithLexeme segment index "where" with
    | some index =>
        match boundaryBreak? segment index 0 with
        | some breakPoint => [breakPoint]
        | none => []
    | none => []
  valueBreak ++ whereBreak

def annotatedDeclarationBreaks (_context : RuleContext) (segment : Segment)
    : List BreakPoint :=
  if childStartsWithLexeme segment 0 "@[" then
    match boundaryBreak? segment 1 0 with
    | some breakPoint => [breakPoint]
    | none => []
  else
    []

def derivingBreaks (_context : RuleContext) (segment : Segment) : List BreakPoint :=
  match segment.indexes.find?
          fun index => childStartsWithLexeme segment index "deriving" with
  | some index =>
      match boundaryBreak? segment index 0 with
      | some breakPoint => [breakPoint]
      | none => []
  | none => []

def structureBreaks (context : RuleContext) (segment : Segment) : List BreakPoint :=
  let fieldsBreak :=
    match firstChildRawKind? segment `Lean.Parser.Command.structFields with
    | some index =>
        match boundaryBreak? segment index 1 with
        | some breakPoint => [breakPoint]
        | none => []
    | none => []
  fieldsBreak ++ derivingBreaks context segment

def structFieldsBreaks (_context : RuleContext) (segment : Segment) : List BreakPoint :=
  match leadingBreak? segment segment.start 1 with
  | some breakPoint => [breakPoint]
  | none => []

def structureFieldBreaks (context : RuleContext) (segment : Segment)
    : List BreakPoint :=
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
          + children.foldl (fun count child => count + structInstFieldChildCount child)
              0
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

def inStructureUpdateFields (context : RuleContext) : Bool :=
  match context.ancestors with
  | parent :: grandparent :: _ =>
      parent.rawKind? == some `Lean.Parser.Term.structInstFields
      && grandparent.rawKind? == some `Lean.Parser.Term.structInst
      && structInstHasWith (Segment.ofTree grandparent.segment.parent)
  | _ => false

def structInstFieldBreaks (context : RuleContext) (segment : Segment)
    : List BreakPoint :=
  if parentIsRawKind context `Lean.Parser.Term.structInstFields then
    match structInstFieldIndexes segment with
    | [] => []
    | [_] => []
    | first :: rest =>
        let indentLevels := if inStructureUpdateFields context then 0 else 1
        let firstBreak :=
          match leadingBreak? segment first indentLevels with
          | some breakPoint => [breakPoint]
          | none => []
        firstBreak
        ++ rest.filterMap fun index => boundaryBreak? segment index indentLevels
  else
    []

def structInstFieldValueBreaks (_context : RuleContext) (segment : Segment)
    : List BreakPoint :=
  match segment.indexes.find? fun index => childStartsWithLexeme segment index ":=" with
  | some assignmentIndex =>
      match (nonemptyChildIndexes segment).find?
              fun index => assignmentIndex < index with
      | some valueIndex =>
          match boundaryBreak? segment valueIndex 1 with
          | some breakPoint => [breakPoint]
          | none => []
      | none => []
  | none => []

def tupleItemIndexes (segment : Segment) : List Nat :=
  segment.indexes.filter
    fun index =>
      match segment.child? index with
      | some child => treeHasContent child && treeFirstLexeme? child != some ","
      | none => false

def tupleItemCount (segment : Segment) : Nat :=
  match firstChildRawKind? segment `null with
  | some index =>
      match segment.child? index with
      | some child => tupleItemIndexes (Segment.ofTree child) |>.length
      | none => 0
  | none => 0

def tupleBreaks (_context : RuleContext) (segment : Segment) : List BreakPoint :=
  if 1 < tupleItemCount segment then
    let itemBreak :=
      match firstChildRawKind? segment `null with
      | some index =>
          match boundaryBreak? segment index 1 with
          | some breakPoint => [breakPoint]
          | none => []
      | none => []
    let closeBreak :=
      match segment.indexes.find?
              fun index => childStartsWithLexeme segment index ")" with
      | some index =>
          match boundaryBreak? segment index 0 with
          | some breakPoint => [breakPoint]
          | none => []
      | none => []
    itemBreak ++ closeBreak
  else
    []

def tupleItemBreaks (context : RuleContext) (segment : Segment) : List BreakPoint :=
  if parentIsRawKind context `Lean.Parser.Term.tuple then
    match tupleItemIndexes segment with
    | [] => []
    | [_] => []
    | _ :: rest =>
        rest.filterMap fun index => boundaryBreak? segment index 0
  else
    []

def arrayItemIndexes (segment : Segment) : List Nat :=
  tupleItemIndexes segment

def arrayItemCount (segment : Segment) : Nat :=
  match firstChildRawKind? segment `null with
  | some index =>
      match segment.child? index with
      | some child => arrayItemIndexes (Segment.ofTree child) |>.length
      | none => 0
  | none => 0

def arrayBreaks (_context : RuleContext) (segment : Segment) : List BreakPoint :=
  if 1 < arrayItemCount segment then
    let itemBreak :=
      match firstChildRawKind? segment `null with
      | some index =>
          match boundaryBreak? segment index 1 with
          | some breakPoint => [breakPoint]
          | none => []
      | none => []
    let closeBreak :=
      match segment.indexes.find?
              fun index => childStartsWithLexeme segment index "]" with
      | some index =>
          match boundaryBreak? segment index 0 with
          | some breakPoint => [breakPoint]
          | none => []
      | none => []
    itemBreak ++ closeBreak
  else
    []

def arrayItemBreaks (context : RuleContext) (segment : Segment) : List BreakPoint :=
  if parentIsRawKind context `«term[_]» || parentIsRawKind context `«term#[_,]» then
    match arrayItemIndexes segment with
    | [] => []
    | [_] => []
    | _ :: rest =>
        rest.filterMap fun index => boundaryBreak? segment index 0
  else
    []

def structInstFieldsMandatory (context : RuleContext) (segment : Segment) : Bool :=
  parentIsRawKind context `Lean.Parser.Term.structInstFields
  && hasMissingCommaBetweenFields segment (structInstFieldIndexes segment)

def structInstBreaks (_context : RuleContext) (segment : Segment) : List BreakPoint :=
  if 1 < structInstFieldCount segment || structInstHasWith segment then
    let hasWith := structInstHasWith segment
    let updateSourceBreak :=
      if hasWith then
        match segment.indexes.find?
                fun index => childStartsWithLexeme segment index "{" with
        | some openIndex =>
            match (nonemptyChildIndexes segment).find?
                    fun index => openIndex < index with
            | some index =>
                match boundaryBreak? segment index 1 with
                | some breakPoint => [breakPoint]
                | none => []
            | none => []
        | none => []
      else
        []
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
    let closeBreak :=
      match segment.indexes.find?
              fun index => childStartsWithLexeme segment index "}" with
      | some index =>
          match boundaryBreak? segment index 0 with
          | some breakPoint => [breakPoint]
          | none => []
      | none => []
    updateSourceBreak ++ fieldBreak ++ closeBreak
  else
    []

/-! ### Declaration lists and module commands -/

def inductiveAlternativeBreaks (context : RuleContext) (segment : Segment)
    : List BreakPoint :=
  if parentIsRawKind context `Lean.Parser.Command.inductive then
    match segment.indexes.filter
            fun index => childStartsWithLexeme segment index "|" with
    | [] => []
    | _ :: rest =>
        rest.filterMap fun index => boundaryBreak? segment index 0
  else
    []

def quantifierBinderBreaks (context : RuleContext) (segment : Segment)
    : List BreakPoint :=
  if quantifierBinderSequence context then
    match nonemptyChildIndexes segment with
    | [] => []
    | [_] => []
    | _ :: rest => rest.filterMap fun index => boundaryBreak? segment index 2
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

def exportItemBreaks (context : RuleContext) (segment : Segment) : List BreakPoint :=
  if exportIdentifierList context then
    match nonemptyChildIndexes segment with
    | [] => []
    | [_] => []
    | _ :: rest => rest.filterMap fun index => boundaryBreak? segment index 0
  else
    []

def moduleImportBreaks (context : RuleContext) (segment : Segment) : List BreakPoint :=
  if parentIsRawKind context `Lean.Parser.Module.header then
    match nonemptyChildIndexes segment with
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

def exportBreaks (_context : RuleContext) (segment : Segment) : List BreakPoint :=
  let listBreak :=
    match boundaryBreak? segment 3 1 with
    | some breakPoint => [breakPoint]
    | none => []
  let closeBreak :=
    match segment.indexes.find?
            fun index => childStartsWithLexeme segment index ")" with
    | some index =>
        match boundaryBreak? segment index 0 with
        | some breakPoint => [breakPoint]
        | none => []
    | none => []
  listBreak ++ closeBreak

/-! ### Applications, signatures, and binders -/

def applicationBreaks (_context : RuleContext) (segment : Segment) : List BreakPoint :=
  childBoundaryBreaks segment 1

def pipeProjBreaks (_context : RuleContext) (segment : Segment) : List BreakPoint :=
  match segment.child? segment.start with
  | some receiver =>
      let receiverHasLineStructure :=
        match receiver.tokens.toList with
        | [] | [_] => false
        | _ :: rest => rest.any fun token => token.leading.text.contains '\n'
      if receiverHasLineStructure then
        match boundaryBreak? segment 1 0 with
        | some breakPoint => [breakPoint]
        | none => []
      else
        []
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
    if parentIsRawKind context `Lean.Parser.Command.optDeclSig
        && grandparentIsRawKind context `Lean.Parser.Command.ctor then
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

def binderBreaks (_context : RuleContext) (segment : Segment) : List BreakPoint :=
  [breakBeforeLexeme? segment ":" 1].filterMap id

/-! ### Application, signature, and binder rule values -/

def applicationRule : LineBreakRule :=
  {
    name := "application"
    flow := fun _ _ => true
    inheritBase := fun _ _ => false
    breakPoints := applicationBreaks
  }

def pipeProjRule : LineBreakRule :=
  {
    name := "pipeProj"
    flow := fun _ _ => true
    inheritBase := fun _ _ => true
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
    inheritBase := fun context _ => parentIsSignatureParameters context
    breakPoints := binderBreaks
  }

/-! ### Bindings and `do` syntax -/

def letBreaks (_context : RuleContext) (segment : Segment) : List BreakPoint :=
  match boundaryBreak? segment 4 0 with
  | some breakPoint => [breakPoint]
  | none => []

def letRecBreaks (_context : RuleContext) (segment : Segment) : List BreakPoint :=
  match boundaryBreak? segment 3 0 with
  | some breakPoint => [breakPoint]
  | none => []

def letRecEquationBreaks (_context : RuleContext) (segment : Segment)
    : List BreakPoint :=
  match firstChildRawKind? segment `Lean.Parser.Term.matchAlts with
  | some index =>
      match boundaryBreak? segment index 1 with
      | some breakPoint => [breakPoint]
      | none => []
  | none => []

def doTryBreaks (_context : RuleContext) (segment : Segment) : List BreakPoint :=
  [boundaryBreak? segment 1 1, boundaryBreak? segment 2 0].filterMap id

def doCatchBreaks (_context : RuleContext) (segment : Segment) : List BreakPoint :=
  match boundaryBreak? segment 4 1 with
  | some breakPoint => [breakPoint]
  | none => []

def doForBreaks (_context : RuleContext) (segment : Segment) : List BreakPoint :=
  [breakAfterLexeme? segment "do" 1].filterMap id

def doForHeaderBreaks (_context : RuleContext) (segment : Segment) : List BreakPoint :=
  [breakBeforeLexeme? segment "in" 2].filterMap id

def doUnlessBreaks (_context : RuleContext) (segment : Segment) : List BreakPoint :=
  [breakAfterLexeme? segment "do" 1].filterMap id

def fromTermBreaks (_context : RuleContext) (segment : Segment) : List BreakPoint :=
  [delimiterValueBreak? segment "from"].filterMap id

def doIfBreaks (_context : RuleContext) (segment : Segment) : List BreakPoint :=
  let thenBreak := boundaryBreak? segment 3 1
  let elseBreaks :=
    (segment.indexes.filter fun index => 4 <= index).filterMap
      fun index =>
        match segment.child? index with
        | some child =>
            if treeHasContent child then boundaryBreak? segment index 0 else none
        | none => none
  [thenBreak].filterMap id ++ elseBreaks

def doSeqItemBreaks (context : RuleContext) (segment : Segment) : List BreakPoint :=
  if parentIsRawKind context `Lean.Parser.Term.doSeqIndent then
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

def letIdDeclBreaks (_context : RuleContext) (segment : Segment) : List BreakPoint :=
  let returnBreak :=
    match segment.child? 1 with
    | some parameters =>
        if treeHasContent parameters then breakBeforeLexeme? segment ":" 2 else none
    | none => none
  [returnBreak, declarationValueBreak? segment].filterMap id

def letPatternDeclBreaks (_context : RuleContext) (segment : Segment)
    : List BreakPoint :=
  [breakAfterLexeme? segment ":=" 1].filterMap id

def doIdDeclBreaks (_context : RuleContext) (segment : Segment) : List BreakPoint :=
  match segment.indexes.find? fun index => childStartsWithLexeme segment index "←" with
  | some assignmentIndex =>
      match (nonemptyChildIndexes segment).find?
              fun index => assignmentIndex < index with
      | some rhsIndex =>
          match boundaryBreak? segment rhsIndex 1 with
          | some breakPoint => [breakPoint]
          | none => []
      | none => []
  | none => []

def doPatternDeclBreaks (_context : RuleContext) (segment : Segment)
    : List BreakPoint :=
  match segment.indexes.find? fun index => childStartsWithLexeme segment index "←" with
  | some assignmentIndex =>
      match (nonemptyChildIndexes segment).find?
              fun index => assignmentIndex < index with
      | some rhsIndex =>
          match boundaryBreak? segment rhsIndex 1 with
          | some breakPoint => [breakPoint]
          | none => []
      | none => []
  | none => []

def doLetElseBreaks (_context : RuleContext) (segment : Segment) : List BreakPoint :=
  let continuationBreak := do
    let pipeIndex ←
      segment.indexes.find? fun index => childStartsWithLexeme segment index "|"
    let fallbackIndex ←
      (nonemptyChildIndexes segment).find? fun index => pipeIndex < index
    let continuationIndex ←
      (nonemptyChildIndexes segment).find? fun index => fallbackIndex < index
    boundaryBreak? segment continuationIndex 0
  [
    breakAfterLexeme? segment ":=" 1,
    breakBeforeLexeme? segment "|" 0,
    continuationBreak
  ].filterMap
    id

/-! ### Binding and `do` rule values -/

def letRule : LineBreakRule :=
  {
    name := "let"
    mandatory := fun _ _ => true
    -- Put `let` on an indentation column so the RHS and body can both use the
    -- ordinary indentation formulas while still satisfying Lean's layout parser.
    alignStartToIndentation := fun _ _ => true
    breakPoints := letBreaks
  }

def letRecRule : LineBreakRule :=
  {
    name := "letRec"
    mandatory := fun _ _ => true
    alignStartToIndentation := fun _ _ => true
    breakPoints := letRecBreaks
  }

def letIdDeclRule : LineBreakRule :=
  {
    name := "letIdDecl"
    inheritBase := fun _ _ => true
    breakPoints := letIdDeclBreaks
  }

def letPatternDeclRule : LineBreakRule :=
  {
    name := "letPatternDecl"
    inheritBase := fun _ _ => true
    breakPoints := letPatternDeclBreaks
  }

def doLetRule : LineBreakRule :=
  {
    name := "doLet"
    inheritBase := fun _ _ => true
  }

def doLetElseRule : LineBreakRule :=
  {
    name := "doLetElse"
    flow := fun _ _ => true
    inheritBase := fun _ _ => true
    breakPoints := doLetElseBreaks
  }

def doIdDeclRule : LineBreakRule :=
  {
    name := "doIdDecl"
    inheritBase := fun _ _ => true
    breakPoints := doIdDeclBreaks
  }

def doPatternDeclRule : LineBreakRule :=
  {
    name := "doPatternDecl"
    inheritBase := fun _ _ => true
    breakPoints := doPatternDeclBreaks
  }

/-! ### Declaration suffixes and recursive declarations -/

def whereDeclsBreaks (_context : RuleContext) (segment : Segment) : List BreakPoint :=
  let leading :=
    match leadingBreak? segment segment.start 0 with
    | some breakPoint => [breakPoint]
    | none => []
  let body :=
    match boundaryBreak? segment 1 1 with
    | some breakPoint => [breakPoint]
    | none => []
  leading ++ body

def whereStructInstBreaks (_context : RuleContext) (segment : Segment)
    : List BreakPoint :=
  match boundaryBreak? segment 1 1 with
  | some breakPoint => [breakPoint]
  | none => []

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

def whereStructInstRule : LineBreakRule :=
  {
    name := "whereStructInst"
    useExistingBreaks := fun _ _ => true
    inheritBase := fun _ _ => true
    breakPoints := whereStructInstBreaks
  }

def rawDefinitionBreaks (_context : RuleContext) (segment : Segment)
    : List BreakPoint :=
  match boundaryBreak? segment 3 1 with
  | some breakPoint => [breakPoint]
  | none => []

def theoremBreaks (_context : RuleContext) (segment : Segment) : List BreakPoint :=
  if childIsRawKind segment 3 `Lean.Parser.Command.declValEqns then
    match boundaryBreak? segment 3 1 with
    | some breakPoint => [breakPoint]
    | none => []
  else
    []

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
    mandatory :=
      fun context segment => !(annotatedDeclarationBreaks context segment).isEmpty
    breakPoints := annotatedDeclarationBreaks
  }

def structureRule : LineBreakRule :=
  {
    name := "structure"
    mandatory := fun context segment => !(structureBreaks context segment).isEmpty
    useExistingBreaks := fun _ _ => true
    breakPoints := structureBreaks
  }

def exportRule : LineBreakRule :=
  {
    name := "export"
    breakPoints := exportBreaks
  }

def definitionRule : LineBreakRule :=
  {
    name := "definition"
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
    accumulatesInfixLeftDepth := fun _ segment => structInstHasWith segment
    breakPoints := structInstBreaks
  }

def tupleRule : LineBreakRule :=
  {
    name := "tuple"
    inheritBase := fun _ _ => true
    breakPoints := tupleBreaks
  }

def structInstFieldsRule : LineBreakRule :=
  {
    name := "structInstFields"
    inheritBase := fun _ _ => true
  }

def structInstFieldRule : LineBreakRule :=
  {
    name := "structInstField"
    useExistingBreaks := fun _ _ => true
    breakPoints := structInstFieldValueBreaks
  }

def structFieldsRule : LineBreakRule :=
  {
    name := "structFields"
    mandatory := fun context segment => !(structFieldsBreaks context segment).isEmpty
    inheritBase := fun _ _ => true
    breakPoints := structFieldsBreaks
  }

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

def ifThenElseKind (kind : Lean.SyntaxNodeKind) : Bool :=
  kind == `termIfThenElse

def ifThenElseElseBranch (context : RuleContext) : Bool :=
  match context.ancestors with
  | parent :: _ =>
      match parent.rawKind? with
      | some kind => ifThenElseKind kind && parent.childIndex == 5
      | none => false
  | _ => false

def ifThenElseElseBranchIsIf (segment : Segment) : Bool :=
  match segment.child? 5 with
  | some (.node (.raw kind) _) => ifThenElseKind kind
  | _ => false

def ifThenElseBreaks (_context : RuleContext) (segment : Segment) : List BreakPoint :=
  let breakSpecs :=
    if ifThenElseElseBranchIsIf segment then
      [(3, 1), (4, 0)]
    else
      [(3, 1), (4, 0), (5, 1)]
  breakSpecs.filterMap
    fun (index, indentLevels) => boundaryBreak? segment index indentLevels

def matchExpressionBreaks (_context : RuleContext) (segment : Segment)
    : List BreakPoint :=
  match firstChildRawKind? segment `Lean.Parser.Term.matchAlts with
  | some index =>
      match boundaryBreak? segment index 0 with
      | some breakPoint => [breakPoint]
      | none => []
  | none => []

def quantifierKind (kind : Lean.SyntaxNodeKind) : Bool :=
  rawKindIsQuantifier kind

def quantifierBodyIndex? (segment : Segment) : Option Nat :=
  (segment.parentIndexes.filter
    fun index =>
      match segment.parentChild? index with
      | some child => treeHasContent child
      | none => false).getLast?

def quantifierBreaks (_context : RuleContext) (segment : Segment) : List BreakPoint :=
  match segment.parent with
  | .node (.raw kind) _ =>
      match quantifierBodyIndex? segment with
      | some bodyIndex =>
          if quantifierKind kind then
            let bodyIsSameQuantifier :=
              match segment.child? bodyIndex with
              | some (.node (.raw childKind) _) => childKind == kind
              | _ => false
            match boundaryBreak? segment bodyIndex
                    (if bodyIsSameQuantifier then 0 else 1) with
            | some breakPoint => [breakPoint]
            | none => []
          else
            []
      | none => []
  | _ => []

def basicFunBreaks (_context : RuleContext) (segment : Segment) : List BreakPoint :=
  match boundaryBreak? segment 3 1 with
  | some breakPoint => [breakPoint]
  | none => []

def subtypeBreaks (_context : RuleContext) (segment : Segment) : List BreakPoint :=
  match boundaryBreak? segment 3 1 with
  | some breakPoint => [breakPoint]
  | none => []

def matchAltRhsIndentLevels (_context : RuleContext) (_segment : Segment) : Nat :=
  2

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

def matchAltBreaks (context : RuleContext) (segment : Segment) : List BreakPoint :=
  if childIsRawKind segment 3 `Lean.Parser.Term.byTactic
      || attachedBodyStart segment 3 then
    []
  else
    match boundaryBreak? segment 3 (matchAltRhsIndentLevels context segment) with
    | some breakPoint => [breakPoint]
    | none => []

def doBreaks (context : RuleContext) (segment : Segment) : List BreakPoint :=
  let indentLevels :=
    if inMatchAltRhs context then
      matchAltRhsIndentLevels context segment
    else
      1
  match boundaryBreak? segment 1 indentLevels with
  | some breakPoint => [breakPoint]
  | none => []

def matchAltsWhereDeclsBreaks (_context : RuleContext) (segment : Segment)
    : List BreakPoint :=
  match leadingBreak? segment segment.start 0 with
  | some breakPoint => [breakPoint]
  | none => []

def matchAltsBreaks (_context : RuleContext) (segment : Segment) : List BreakPoint :=
  segment.indexes.filterMap fun index => leadingBreak? segment index 0

/-! ### Infix expressions and generic wrappers -/

def infixBreaks (_context : RuleContext) (segment : Segment) : List BreakPoint :=
  match segment.parent with
  | .node (.infixChain `Lean.Parser.Term.proj) _ => []
  | _ =>
      match segment.children? with
      | none => []
      | some children =>
          (List.range children.size).filterMap
            fun index =>
              if index % 2 == 1 then
                boundaryBreak? segment index 0
              else
                none

def commandInBreaks (_context : RuleContext) (segment : Segment) : List BreakPoint :=
  match boundaryBreak? segment 2 0 with
  | some breakPoint => [breakPoint]
  | none => []

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
  | _ => false

def frameIsQuantifierBody (frame : Frame) : Bool :=
  match frame.segment.parent with
  | .node (.raw kind) _ =>
      quantifierKind kind && quantifierBodyIndex? frame.segment == some frame.childIndex
  | _ => false

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
  arrowInfixSegment segment && !arrowInfixLogicalContext context

def nullBreaks (context : RuleContext) (segment : Segment) : List BreakPoint :=
  structureFieldBreaks context segment
  ++ structInstFieldBreaks context segment
  ++ tupleItemBreaks context segment
  ++ arrayItemBreaks context segment
  ++ inductiveAlternativeBreaks context segment
  ++ quantifierBinderBreaks context segment
  ++ binderIdentifierBreaks context segment
  ++ exportItemBreaks context segment
  ++ doSeqItemBreaks context segment
  ++ doElseBreaks context segment
  ++ doElseIfBreaks context segment
  ++ doElseIfChainBreaks context segment
  ++ moduleImportBreaks context segment
  ++ moduleCommandBreaks context segment

def nullBreaksMandatory (context : RuleContext) (segment : Segment) : Bool :=
  !(structureFieldBreaks context segment).isEmpty
  || structInstFieldsMandatory context segment
  || !(inductiveAlternativeBreaks context segment).isEmpty
  || !(doSeqItemBreaks context segment).isEmpty
  || !(doElseBreaks context segment).isEmpty
  || !(doElseIfBreaks context segment).isEmpty
  || !(doElseIfChainBreaks context segment).isEmpty
  || !(moduleImportBreaks context segment).isEmpty
  || !(moduleCommandBreaks context segment).isEmpty

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
        !(quantifierBinderBreaks context segment).isEmpty
        || !(binderIdentifierBreaks context segment).isEmpty
        || !(exportItemBreaks context segment).isEmpty
    inheritBase := nullInheritBase
    breakPoints := nullBreaks
  }

def arrayRule : LineBreakRule :=
  {
    name := "array"
    inheritBase := fun _ segment => 1 < arrayItemCount segment
    breakPoints := arrayBreaks
  }

def declarationRule : LineBreakRule :=
  { name := "declaration" }

def declarationValueRule : LineBreakRule :=
  {
    name := "declarationValue"
    inheritBase := fun _ _ => true
    breakPoints := declarationValueBreaksWithoutNestedBody
  }

def letRecDeclarationRule : LineBreakRule :=
  {
    name := "letRecDeclaration"
    inheritBase := fun _ _ => true
  }

def letRecEquationRule : LineBreakRule :=
  {
    name := "letRecEquation"
    mandatory := fun _ _ => true
    inheritBase := fun _ _ => true
    breakPoints := letRecEquationBreaks
  }

def moduleRule : LineBreakRule :=
  { name := "module" }

def setOptionRule : LineBreakRule :=
  {
    name := "setOption"
    useExistingBreaks := fun _ _ => true
    breakPoints := setOptionBreaks
  }

def transparentRule : LineBreakRule :=
  { name := "transparent" }

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
    flow := infixFlow
    accumulatesInfixLeftDepth := fun _ _ => true
    breakPoints := infixBreaks
  }

def commandInChainRule : LineBreakRule :=
  {
    name := "commandInChain"
    breakPoints := commandInBreaks
  }

def ifThenElseRule : LineBreakRule :=
  {
    name := "ifThenElse"
    useExistingBreaks := fun _ _ => true
    inheritBase := fun context _ => ifThenElseElseBranch context
    breakPoints := ifThenElseBreaks
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
    inheritBase := fun _ _ => true
    breakPoints := basicFunBreaks
  }

def prefixedTermRule (name : String) : LineBreakRule :=
  {
    name
    inheritBase := fun _ _ => true
  }

def bangPrefixRule : LineBreakRule :=
  prefixedTermRule "bangPrefix"

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

def doForHeaderRule : LineBreakRule :=
  {
    name := "doForHeader"
    inheritBase := fun _ _ => true
    accumulatesInfixLeftDepth := fun _ _ => true
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

def doIfRule : LineBreakRule :=
  {
    name := "doIf"
    mandatory := fun _ _ => true
    inheritBase := fun _ _ => true
    breakPoints := doIfBreaks
  }

def groupBreaks (context : RuleContext) (segment : Segment) : List BreakPoint :=
  let elseIfBreaks := doElseIfBreaks context segment
  if elseIfBreaks.isEmpty then defaultBreaks context segment else elseIfBreaks

def groupRule : LineBreakRule :=
  {
    name := "group"
    useExistingBreaks :=
      fun context segment =>
        (doElseIfBreaks context segment).isEmpty
        && !(defaultBreaks context segment).isEmpty
    mandatory := fun context segment => !(doElseIfBreaks context segment).isEmpty
    flow :=
      fun context segment =>
        (doElseIfBreaks context segment).isEmpty
        && !(defaultBreaks context segment).isEmpty
        && !defaultIsInfix context segment
    accumulatesInfixLeftDepth :=
      fun context segment =>
        (doElseIfBreaks context segment).isEmpty && defaultIsInfix context segment
    breakPoints := groupBreaks
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

def ruleFor : SyntaxTree.Tree → Option LineBreakRule
  | .missing => some defaultRule
  | .leaf _ => some defaultRule
  -- Module and declaration wrappers with generic layout.
  | .node (.raw `null) _ => some nullRule
  | .node (.raw `Lean.Parser.Module.module) _ => some moduleRule
  | .node (.raw `Lean.Parser.Module.header) _ => some moduleRule
  | .node (.raw `Lean.Parser.Module.import) _ => some moduleRule
  | .node (.raw `Lean.Parser.Module.moduleTk) _ => some defaultRule
  | .node (.raw `Lean.Parser.Module.public) _ => some defaultRule
  | .node (.raw `Lean.Parser.Module.meta) _ => some defaultRule
  | .node (.raw `Lean.Parser.Command.moduleDoc) _ => some defaultRule
  | .node (.raw `Lean.Parser.Command.docComment) _ => some defaultRule
  | .node (.raw `Lean.Parser.Command.sectionHeader) _ => some defaultRule
  | .node (.raw `Lean.Parser.Command.namespace) _ => some defaultRule
  | .node (.raw `Lean.Parser.Command.end) _ => some defaultRule
  | .node (.raw `Lean.Parser.Command.open) _ => some defaultRule
  | .node (.raw `Lean.Parser.Command.openSimple) _ => some defaultRule
  | .node (.raw `Lean.Parser.Command.openScoped) _ => some defaultRule
  | .node (.raw `Lean.Parser.Command.variable) _ => some defaultRule
  | .node (.raw `Lean.Parser.Command.set_option) _ => some setOptionRule
  | .node (.raw `Lean.Parser.Command.declModifiers) _ => some defaultRule
  | .node (.raw `Lean.Parser.Command.declId) _ => some transparentRule
  | .node (.raw `Lean.Parser.Command.declValEqns) _ => some defaultRule
  | .node (.raw `Lean.Parser.Command.optDeriving) _ => some defaultRule
  | .node (.raw `Lean.Parser.Command.derivingClass) _ => some defaultRule
  | .node (.raw `Lean.Parser.Command.structureTk) _ => some defaultRule
  | .node (.raw `Lean.Parser.Command.classTk) _ => some defaultRule
  | .node (.raw `Lean.Parser.Command.private) _ => some defaultRule
  | .node (.raw `Lean.Parser.Command.public) _ => some defaultRule
  | .node (.raw `Lean.Parser.Command.meta) _ => some defaultRule
  | .node (.raw `Lean.Parser.Command.noncomputable) _ => some defaultRule
  | .node (.raw `Lean.Parser.Command.protected) _ => some defaultRule
  | .node (.raw `Lean.Parser.Command.partial) _ => some defaultRule
  | .node (.raw `Lean.Parser.Command.eval) _ => some defaultRule
  | .node (.raw `Lean.Parser.Command.check) _ => some defaultRule
  | .node (.raw `Lean.Parser.Command.example) _ => some defaultRule
  | .node (.raw `Lean.Parser.Command.universe) _ => some defaultRule
  | .node (.raw `Lean.Parser.Command.syntax) _ => some defaultRule
  | .node (.raw `Lean.Parser.Command.macro_rules) _ => some defaultRule
  | .node (.raw `Lean.Parser.Command.attribute) _ => some defaultRule
  | .node (.raw `Lean.Parser.Command.deprecated_module) _ => some defaultRule
  | .node (.raw `Lean.Parser.Command.assertNotImported) _ => some defaultRule
  | .node (.raw `Lean.Parser.Command.assertNotExists) _ => some defaultRule
  | .node (.raw `Lean.Parser.Command.namedPrio) _ => some defaultRule
  | .node (.raw `Lean.Parser.Command.abbrev) _ => some defaultRule
  | .node (.raw `Lean.Parser.Command.classAbbrev) _ => some defaultRule
  | .node (.raw `Lean.Parser.Command.nonrec) _ => some defaultRule
  | .node (.raw `Lean.Parser.Command.notation) _ => some defaultRule
  | .node (.raw `Lean.Parser.Command.identPrec) _ => some defaultRule
  | .node (.raw `Lean.Parser.Command.grindPattern) _ => some defaultRule
  | .node (.raw `Lean.Parser.Command.omit) _ => some defaultRule
  | .node (.raw `Lean.Parser.Command.structParent) _ => some defaultRule
  | .node (.raw `Lean.Parser.Command.structCtor) _ => some defaultRule
  | .node (.raw `Lean.Parser.Command.structInstBinder) _ => some defaultRule
  | .node (.raw `Lean.Parser.Command.extends) _ => some defaultRule
  | .node (.raw `Lean.Parser.Command.initialize_simps_projections) _ => some defaultRule
  | .node (.raw `Lean.Parser.Command.simpsProj) _ => some defaultRule
  | .node (.raw `Lean.Parser.Command.simpsRule) _ => some defaultRule
  | .node (.raw `Lean.Parser.Command.simpsRule.prefix) _ => some defaultRule
  | .node (.raw `Lean.Parser.Command.simpsRule.erase) _ => some defaultRule
  | .node (.raw `lemma) _ => some defaultRule
  -- Transparent expression wrappers and atomic syntax.
  | .node (.raw `Lean.Parser.Term.paren) _ => some parenRule
  | .node (.raw `Lean.Parser.Term.fun) _ => some transparentRule
  | .node (.raw `Lean.Parser.Term.nestedAction) _ => some nestedActionRule
  | .node (.raw `Lean.Parser.Term.unsafe) _ => some unsafeTermRule
  | .node (.raw `Lean.Parser.Term.typeSpec) _ => some transparentRule
  | .node (.raw `Lean.Parser.Command.declValSimple) _ =>
      some declarationValueRule
  | .node (.raw `Lean.Parser.Command.instance) _ => some transparentRule
  | .node (.raw `Lean.Parser.Command.ctor) _ => some transparentRule
  | .node (.raw `Lean.Parser.Command.structSimpleBinder) _ => some transparentRule
  | .node (.raw `Lean.Parser.Term.structInstField) _ => some structInstFieldRule
  | .node (.raw `Lean.Parser.Term.structInstFieldDef) _ => some transparentRule
  | .node (.raw `Lean.Parser.Term.structInstLVal) _ => some transparentRule
  | .node (.raw `Lean.Parser.Term.namedPattern) _ => some transparentRule
  | .node (.raw `Lean.Parser.Term.pipeProj) _ => some pipeProjRule
  | .node (.raw `Lean.Parser.Term.hygienicLParen) _ => some defaultRule
  | .node (.raw `hygieneInfo) _ => some defaultRule
  | .node (.raw `Lean.Parser.Term.type) _ => some defaultRule
  | .node (.raw `Lean.Parser.Term.prop) _ => some defaultRule
  | .node (.raw `Lean.Parser.Term.typeAscription) _ => some defaultRule
  | .node (.raw `Lean.Parser.Term.optEllipsis) _ => some defaultRule
  | .node (.raw `Lean.Parser.Term.explicit) _ => some defaultRule
  | .node (.raw `Lean.Parser.Term.explicitUniv) _ => some defaultRule
  | .node (.raw `Lean.Parser.Term.have) _ => some defaultRule
  | .node (.raw `Lean.Parser.Term.haveI) _ => some defaultRule
  | .node (.raw `Lean.Parser.Term.hole) _ => some defaultRule
  | .node (.raw `Lean.Parser.Term.syntheticHole) _ => some defaultRule
  | .node (.raw `Lean.Parser.Term.sort) _ => some defaultRule
  | .node (.raw `Lean.Parser.Term.letConfig) _ => some defaultRule
  | .node (.raw `Lean.Parser.Term.letDecl) _ => some defaultRule
  | .node (.raw `Lean.Parser.Term.letI) _ => some defaultRule
  | .node (.raw `Lean.Parser.Term.inferInstanceAs) _ => some defaultRule
  | .node (.raw `Lean.Parser.Term.configItem) _ => some defaultRule
  | .node (.raw `Lean.Parser.Term.negConfigItem) _ => some defaultRule
  | .node (.raw `Lean.Parser.Term.letRecDecls) _ => some letRecDeclarationRule
  | .node (.raw `Lean.Parser.Term.letRecDecl) _ => some letRecDeclarationRule
  | .node (.raw `Lean.Parser.Term.letEqnsDecl) _ => some letRecEquationRule
  | .node (.raw `Lean.Parser.Term.letId) _ => some defaultRule
  | .node (.raw `Lean.Parser.Term.letIdDeclNoBinders) _ => some letIdDeclRule
  | .node (.raw `Lean.Parser.Term.matchDiscr) _ => some transparentRule
  | .node (.raw `Lean.Parser.Term.binderDefault) _ => some defaultRule
  | .node (.raw `Lean.Parser.Term.namedArgument) _ => some defaultRule
  | .node (.raw `Lean.Parser.Term.strictImplicitBinder) _ => some defaultRule
  | .node (.raw `Lean.Parser.Term.anonymousCtor) _ => some defaultRule
  | .node (.raw `Lean.Parser.Term.local) _ => some defaultRule
  | .node (.raw `Lean.Parser.Term.instBinder) _ => some defaultRule
  | .node (.raw `Lean.Parser.Term.attrKind) _ => some defaultRule
  | .node (.raw `Lean.Parser.Term.attrInstance) _ => some defaultRule
  | .node (.raw `Lean.Parser.Term.attributes) _ => some defaultRule
  | .node (.raw `Lean.Parser.Term.scoped) _ => some defaultRule
  | .node (.raw `Lean.Parser.Term.ellipsis) _ => some defaultRule
  | .node (.raw `Lean.Parser.Term.nomatch) _ => some defaultRule
  | .node (.raw `Lean.Parser.Term.quotedName) _ => some defaultRule
  | .node (.raw `Lean.Parser.Term.cdot) _ => some defaultRule
  | .node (.raw `Lean.Parser.Term.show) _ => some transparentRule
  | .node (.raw `Lean.Parser.Term.fromTerm) _ => some fromTermRule
  | .node (.raw `Lean.Parser.Tactic.tacticSeq) _ => some defaultRule
  | .node (.raw `Lean.Parser.Tactic.tacticSeq1Indented) _ => some defaultRule
  -- Known leaf-like parser nodes handled by generic spacing and layout.
  | .node (.raw `Lean.binderIdent) _ => some defaultRule
  | .node (.raw `Lean.explicitBinders) _ => some defaultRule
  | .node (.raw `Lean.unbracketedExplicitBinders) _ => some defaultRule
  | .node (.raw `Lean.bracketedExplicitBinders) _ => some defaultRule
  | .node (.raw `num) _ => some defaultRule
  | .node (.raw `str) _ => some defaultRule
  | .node (.raw `name) _ => some defaultRule
  | .node (.raw `char) _ => some defaultRule
  | .node (.raw `fieldIdx) _ => some defaultRule
  | .node (.raw `patternIgnore) _ => some defaultRule
  | .node (.raw `termℕ) _ => some defaultRule
  | .node (.raw `termℤ) _ => some defaultRule
  | .node (.raw `termℚ) _ => some defaultRule
  | .node (.raw `termℝ) _ => some defaultRule
  | .node (.raw `Lean.Elab.Term.«termType*») _ => some defaultRule
  | .node (.raw `Lean.Elab.Term.«termSort*») _ => some defaultRule
  | .node (.raw `coeNotation) _ => some defaultRule
  | .node (.raw `coeSortNotation) _ => some defaultRule
  | .node (.raw `Lean.calc) _ => some defaultRule
  | .node (.raw `Lean.calcSteps) _ => some defaultRule
  | .node (.raw `Lean.calcFirstStep) _ => some defaultRule
  | .node (.raw `Lean.«term∀__,_») _ => some defaultRule
  | .node (.raw `Lean.«term∃__,_») _ => some defaultRule
  | .node (.raw `Lean.«binderPred∈_») _ => some defaultRule
  | .node (.raw `Lean.«binderPred≤_») _ => some defaultRule
  | .node (.raw `Lean.«binderPred∉_») _ => some defaultRule
  | .node (.raw `termDepIfThenElse) _ => some defaultRule
  | .node (.raw `BigOperators.bigsum) _ => some defaultRule
  | .node (.raw `BigOperators.bigprod) _ => some defaultRule
  | .node (.raw `BigOperators.bigOpBinders) _ => some defaultRule
  | .node (.raw `BigOperators.bigOpBinder) _ => some defaultRule
  | .node (.raw `Batteries.ExtendedBinder.extBinders) _ => some defaultRule
  | .node (.raw `Batteries.ExtendedBinder.extBinder) _ => some defaultRule
  | .node (.raw `Batteries.ExtendedBinder.extBinderCollection) _ => some defaultRule
  | .node (.raw `Batteries.ExtendedBinder.extBinderParenthesized) _ => some defaultRule
  | .node (.raw `choice) _ => some transparentRule
  | .node (.raw `Lean.Parser.Syntax.atom) _ => some transparentRule
  | .node (.raw `Lean.Parser.Syntax.cat) _ => some transparentRule
  | .node (.raw `«stx_,*») _ => some transparentRule
  | .node (.raw `Lean.Parser.Term.quot) _ => some defaultRule
  | .node (.raw `term!_) _ => some bangPrefixRule
  | .node (.raw `«term¬_») _ => some defaultRule
  | .node (.raw `token.«← ») _ => some defaultRule
  | .node (.raw `Lean.Parser.Attr.simp) _ => some defaultRule
  | .node (.raw `Lean.Parser.Attr.grind) _ => some defaultRule
  | .node (.raw `Lean.Parser.Attr.grindMod) _ => some defaultRule
  | .node (.raw `Lean.Parser.Attr.grindEq) _ => some defaultRule
  | .node (.raw `Lean.Parser.Attr.grindEqBoth) _ => some defaultRule
  | .node (.raw `Lean.Parser.Attr.grindDef) _ => some defaultRule
  | .node (.raw `Lean.Parser.Attr.grindLR) _ => some defaultRule
  | .node (.raw `Lean.Parser.Attr.grindFwd) _ => some defaultRule
  | .node (.raw `Lean.Parser.Attr.grindBwd) _ => some defaultRule
  | .node (.raw `Lean.Parser.Attr.simple) _ => some defaultRule
  | .node (.raw `Lean.Parser.Attr.simps) _ => some defaultRule
  | .node (.raw `Lean.Parser.Attr.attrSimps!_) _ => some defaultRule
  | .node (.raw `Lean.Parser.Attr.simpsArgsRest) _ => some defaultRule
  | .node (.raw `Lean.Parser.Attr.simpsConfig) _ => some defaultRule
  | .node (.raw `Lean.Parser.Attr.simpsConfigItem) _ => some defaultRule
  | .node (.raw `Lean.Parser.Attr.norm_cast) _ => some defaultRule
  | .node (.raw `Lean.Parser.Attr.ext) _ => some defaultRule
  | .node (.raw `Lean.Attr.coe) _ => some defaultRule
  | .node (.raw `Lean.Parser.Attr.instance) _ => some defaultRule
  | .node (.raw `Lean.deprecated) _ => some defaultRule
  | .node (.raw `token.existing) _ => some defaultRule
  | .node (.raw `Mathlib.Tactic.ToAdditive.to_additive) _ => some defaultRule
  | .node (.raw `Mathlib.Tactic.MkIff.mkIff) _ => some defaultRule
  | .node (.raw `Mathlib.Tactic.Translate.attrArgs) _ => some defaultRule
  | .node (.raw `Mathlib.Tactic.Translate.bracketedOption) _ => some defaultRule
  | .node (.raw `Mathlib.Tactic.Translate.translationHint) _ => some defaultRule
  | .node (.raw `«term{}») _ => some defaultRule
  | .node (.raw `Lean.Parser.Level.hole) _ => some defaultRule
  | .node (.raw `«term∅») _ => some defaultRule
  | .node (.raw `«term⊤») _ => some defaultRule
  | .node (.raw `«term⊥») _ => some defaultRule
  | .node (.raw `«term-_») _ => some defaultRule
  | .node (.raw `«term_⁻¹») _ => some defaultRule
  | .node (.raw `«term_ˣ») _ => some defaultRule
  | .node (.raw `«term_ᵐᵒᵖ») _ => some defaultRule
  | .node (.raw `«term__[_]») _ => some defaultRule
  | .node (.raw `«term_→ₗ[_]_») _ => some defaultRule
  | .node (.raw `«term_≃ₗ[_]_») _ => some defaultRule
  | .node (.raw `«term_→ₐ[_]_») _ => some defaultRule
  | .node (.raw `«term_≡_[MOD_]») _ => some defaultRule
  | .node (.raw `«term_≡_[ZMOD_]») _ => some defaultRule
  | .node (.raw `«term⨆_,_») _ => some defaultRule
  | .node (.raw `PiNotation.piNotation) _ => some defaultRule
  | .node (.raw `coeFunNotation) _ => some defaultRule
  | .node (.raw `Mathlib.Meta.setBuilder) _ => some defaultRule
  | .node (.raw `Mathlib.Elab.FastInstance.fastInstance) _ => some defaultRule
  | .node (.raw `Mathlib.Tactic.scopedNS) _ => some defaultRule
  | .node (.raw `Mathlib.Tactic.Push.pushAttr) _ => some defaultRule
  | .node (.raw `Mathlib.Tactic.GCongr.gcongrAttr) _ => some defaultRule
  | .node (.raw `Mathlib.Tactic.Monotonicity.Attr.mono) _ => some defaultRule
  | .node (.raw `Mathlib.CrossRef.wikidataTag) _ => some defaultRule
  | .node (.raw `Parser.Attr.parity_simps) _ => some defaultRule
  | .node (.raw `Parser.Attr.nontriviality) _ => some defaultRule
  | .node (.raw `Batteries.Tactic.Alias.alias) _ => some defaultRule
  | .node (.raw `Batteries.Tactic.Alias.aliasLR) _ => some defaultRule
  | .node (.raw `Batteries.Tactic.Lint.nolint) _ => some defaultRule
  | .node (.raw `Batteries.Util.LibraryNote.commandLibrary_note___) _ =>
      some defaultRule
  | .node (.raw `Aesop.Frontend.Parser.aesop) _ => some defaultRule
  | .node (.raw `Aesop.Frontend.Parser.attr_rules_) _ => some defaultRule
  | .node (.raw `Aesop.Frontend.Parser.rule_expr_) _ => some defaultRule
  | .node (.raw `Aesop.Frontend.Parser.rule_expr___) _ => some defaultRule
  | .node (.raw `Aesop.Frontend.Parser.ruleSetsFeature) _ => some defaultRule
  | .node (.raw `Aesop.Frontend.Parser.feature_) _ => some defaultRule
  | .node (.raw `Aesop.Frontend.Parser.feature__1) _ => some defaultRule
  | .node (.raw `Aesop.Frontend.Parser.feature__2) _ => some defaultRule
  | .node (.raw `Aesop.Frontend.Parser.feature__4) _ => some defaultRule
  | .node (.raw `Aesop.Frontend.Parser.phaseSafe) _ => some defaultRule
  | .node (.raw `Aesop.Frontend.Parser.builder_nameApply) _ => some defaultRule
  | .node (.raw `Aesop.Frontend.Parser.«priority_%») _ => some defaultRule
  | .node (.raw `Aesop.Frontend.Parser.«priority-_») _ => some defaultRule
  | .node (.raw `prioLow) _ => some defaultRule
  | .node (.raw `prioHigh) _ => some defaultRule
  | .node (.raw `cfcTac) _ => some defaultRule
  | .node (.raw `adaptationNoteCmd) _ => some defaultRule
  | .node (.raw `wikidataId) _ => some defaultRule
  | .node (.raw `«term{_}») _ => some structInstRule
  | .node (.raw `«term[_]») _ => some arrayRule
  | .node (.raw `«term#[_,]») _ => some arrayRule
  | .node (.raw `«term__[_]_?») _ => some transparentRule
  -- Syntax with specialized formatting rules.
  | .node (.raw `Lean.Parser.Command.declaration) _ => some declarationRule
  | .node .annotatedDeclaration _ => some annotatedDeclarationRule
  | .node (.raw `Lean.Parser.Command.structure) _ => some structureRule
  | .node (.raw `Lean.Parser.Command.export) _ => some exportRule
  | .node .definition _ => some definitionRule
  | .node (.raw `Lean.Parser.Command.definition) _ => some rawDefinitionRule
  | .node (.raw `Lean.Parser.Command.theorem) _ => some theoremRule
  | .node (.raw `Lean.Parser.Term.structInst) _ => some structInstRule
  | .node (.raw `Lean.Parser.Term.tuple) _ => some tupleRule
  | .node (.raw `Lean.Parser.Term.structInstFields) _ => some structInstFieldsRule
  | .node (.raw `Lean.Parser.Command.structFields) _ => some structFieldsRule
  | .node (.raw `Lean.Parser.Command.inductive) _ => some inductiveRule
  | .node .application _ => some applicationRule
  | .node .signatureParameters _ => some signatureParametersRule
  | .node .matchPatterns _ => some matchPatternsRule
  | .node .matchDiscriminants _ => some matchDiscriminantsRule
  | .node .doForHeader _ => some doForHeaderRule
  | .node (.raw `Lean.Parser.Command.optDeclSig) _ => some signatureRule
  | .node (.raw `Lean.Parser.Command.declSig) _ => some signatureRule
  | .node (.raw `Lean.Parser.Term.explicitBinder) _ => some binderRule
  | .node (.raw `Lean.Parser.Term.implicitBinder) _ => some binderRule
  | .node (.raw `Lean.Parser.Term.let) _ => some letRule
  | .node (.raw `Lean.Parser.Term.letrec) _ => some letRecRule
  | .node (.raw `Lean.Parser.Term.letIdDecl) _ => some letIdDeclRule
  | .node (.raw `Lean.Parser.Term.letPatDecl) _ => some letPatternDeclRule
  | .node (.raw `Lean.Parser.Term.whereDecls) _ => some whereDeclsRule
  | .node (.raw `Lean.Parser.Command.whereStructInst) _ => some whereStructInstRule
  | .node (.raw `Lean.Parser.Command.mutual) _ => some mutualRule
  | .node (.infixChain `Lean.Parser.Command.in) _ => some commandInChainRule
  | .node (.infixChain _) _ => some infixChainRule
  | .node (.raw `termIfThenElse) _ => some ifThenElseRule
  | .node (.raw `Lean.Parser.Term.match) _ => some matchExpressionRule
  | .node (.raw `Lean.Parser.Term.forall) _ => some quantifierRule
  | .node (.raw `Lean.Parser.Term.exists) _ => some quantifierRule
  | .node (.raw `«term∃_,_») _ => some quantifierRule
  | .node (.raw `Lean.Parser.Term.basicFun) _ => some basicFunRule
  | .node (.raw `«term{_:_//_}») _ => some subtypeRule
  | .node (.raw `Lean.Parser.Term.matchAlt) _ => some matchAltRule
  | .node (.raw `Lean.Parser.Term.do) _ => some doRule
  | .node (.raw `Lean.Parser.Term.doLet) _ => some doLetRule
  | .node (.raw `Lean.Parser.Term.doLetElse) _ => some doLetElseRule
  | .node (.raw `Lean.Parser.Term.doMatch) _ => some matchExpressionRule
  | .node (.raw `Lean.Parser.Term.doTry) _ => some doTryRule
  | .node (.raw `Lean.Parser.Term.doCatch) _ => some doCatchRule
  | .node (.raw `Lean.Parser.Term.doFor) _ => some doForRule
  | .node (.raw `Lean.Parser.Term.doIf) _ => some doIfRule
  | .node (.raw `Lean.Parser.Term.doReassign) _ => some transparentRule
  | .node (.raw `Lean.Parser.Term.doReturn) _ => some transparentRule
  | .node (.raw `Lean.Parser.Term.doIfProp) _ => some transparentRule
  | .node (.raw `Lean.Parser.Term.doUnless) _ => some doUnlessRule
  | .node (.raw `Lean.Parser.Term.doForDecl) _ => some transparentRule
  | .node (.raw `Lean.Parser.Term.liftMethod) _ => some transparentRule
  | .node (.raw `Lean.Parser.Term.dotIdent) _ => some defaultRule
  | .node (.raw `termS!_) _ => some interpolatedStringRule
  | .node (.raw `interpolatedStrKind) _ => some interpolatedStringRule
  | .node (.raw `interpolatedStrLitKind) _ => some interpolatedStringRule
  | .node (.raw `Lean.Parser.Term.doSeqIndent) _ => some defaultRule
  | .node (.raw `Lean.Parser.Term.doSeqItem) _ => some defaultRule
  | .node (.raw `Lean.Parser.Term.doExpr) _ => some defaultRule
  | .node (.raw `Lean.Parser.Term.doLetArrow) _ => some doLetRule
  | .node (.raw `Lean.Parser.Term.doIdDecl) _ => some doIdDeclRule
  | .node (.raw `Lean.Parser.Term.doPatDecl) _ => some doPatternDeclRule
  | .node (.raw `group) _ => some groupRule
  | .node (.raw `Lean.Parser.Term.matchAltsWhereDecls) _ => some matchAltsWhereDeclsRule
  | .node (.raw `Lean.Parser.Term.matchAlts) _ => some matchAltsRule
  | .node (.raw _) _ => none

def formattingRuleFor (tree : SyntaxTree.Tree) : LineBreakRule :=
  match ruleFor tree with
  | some rule => rule
  | none => defaultRule

end LineBreakRules
end Formatter
end LeanFmt
