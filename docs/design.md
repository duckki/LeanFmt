# LeanFmt formatting design

This document describes how LeanFmt formats Lean source code. It is written for
Lean programmers evaluating the formatter and for users who want to understand
the changes it makes.

LeanFmt is a conservative, structure-preserving formatter. It parses a complete
Lean file with Lean's parser, recognizes common Lean constructs, and chooses
whitespace and line breaks around the existing source tokens.

For implementation architecture, see [architecture.md](architecture.md). For build,
test, and debugging commands, see [development.md](development.md).

## Formatting at a glance

LeanFmt turns a line-wrapped proposition whose nesting is difficult to scan:

```lean
def parenthesizedConjunctionChain (schema : Schema) : Prop :=
  namesAreUnique (schema.allTypes.map TypeDefinition.name) ∧
    schema.objectType schema.queryType ∧
    (∀ typeDefinition, typeDefinition ∈ schema.types
      -> typeDefinitionWellFormed schema typeDefinition) ∧ (∀ typeName objectTypeName,
          objectTypeName ∈ schema.getPossibleTypes typeName
    -> schema.objectType objectTypeName)
```

into a layout where each leading `∧` connects a peer operand and indentation
shows the structure inside each operand:

```lean
def parenthesizedConjunctionChain (schema : Schema) : Prop :=
  namesAreUnique (schema.allTypes.map TypeDefinition.name)
  ∧ schema.objectType schema.queryType
  ∧ (∀ typeDefinition,
      typeDefinition ∈ schema.types -> typeDefinitionWellFormed schema typeDefinition)
  ∧ (∀ typeName objectTypeName,
      objectTypeName ∈ schema.getPossibleTypes typeName
      -> schema.objectType objectTypeName)
```

## Design philosophy

### Preserve code, format structure

Formatting changes whitespace only. Token text and token order remain the same.

### Prefer a clear rule over a clever guess

LeanFmt has rules for common Lean constructs. Unknown syntax is still lossless and
receives a generic structural layout, but LeanFmt does not guess at the meaning of custom
syntax.

Proofs receive an even more conservative treatment. Proof subtrees are retained
from their original source so that formatting declarations and propositions
does not accidentally damage tactic layout.

### Keep fitting code compact

LeanFmt uses a 90-character default line limit and two-space indentation. The
line limit is configurable for projects with a different convention. Most
constructs are first considered in a single-line form. A construct breaks only
when it is structurally multiline, an accepted source break applies, or the flat
form does not fit.

The line limit counts displayed Lean characters in the formatter's string
model: symbols such as `∀`, `∧`, and `→` count as one character.

### Make continuation structure visible

Indentation shows block structure under constructs such as `def` and `theorem`.
It also shows a local continuation when an application wraps:

```lean
def result :=
  veryLongFunctionName child children additionalArgumentOne
    additionalArgumentTwo additionalArgumentThree
    additionalArgumentFour
```

For infix expressions, a leading operator indicates continuation without adding
another logical nesting level:

```lean
def result : Prop :=
  firstCondition
  ∧ secondCondition
  ∧ finalCondition
```

LeanFmt generally breaks before operators for this reason. Bodies after `:=`,
`=>`, `with`, quantifier commas, and similar separators are indented instead.

### Preserve intentional source breaks selectively

Line breaks from the input source code are meaningful in some places and incidental in
others. LeanFmt preserves a source break only where the rule for that construct accepts
one. It always computes the resulting indentation itself.

For example, a multiline function application may retain well-chosen argument
breaks after the flat form overflows. A fitting infix expression is flattened
even if its source had an arbitrary break.

Input source code with intentional line breaks:

```lean
      semanticEquality schema someLongContextParameter
        (normalize left)
        (normalize right)
```

We don't want to force wrap it like:

```lean
      semanticEquality schema someLongContextParameter (normalize left)
        (normalize right)
```

Definitions, theorems, parameter lists, and match pattern lists also have
specific boundaries where source line breaks may be preserved.

Source-break preservation follows the rule's layout mode:

- a flow rule may retain only the accepted boundaries needed by its fitting layout;
- a non-flow rule is balanced: once an accepted source break activates the rule,
  every break point returned by that rule is applied together.

This prevents partially broken branch, collection, header, and peer layouts. A
non-flow conditional cannot preserve only the break before `else`, for example;
it formats the `then` and `else` branches as one balanced structure.

### Keep separators with their headers

The assignment and arm separators `:=`, `←`, and `=>` belong to the header on
their left. Their syntax rules do not offer a break immediately before the
separator. If the right-hand side must move, the break occurs after it:

```lean
def result :=
  longDefinitionBody

let value :=
  longComputation

let value ←
  longAction

| pattern =>
    longArmBody
```

This rule applies consistently to declarations, ordinary and destructuring
`let` bindings, monadic bindings, lambdas, match alternatives, and
equation-style declaration arms.

The same header-suffix principle keeps `instance ... where` and `match ... with`
together; the body breaks after `where` or `with`, not before it.

The introducer keyword is also part of a binding header. LeanFmt never emits a
line containing only `let`; it keeps `let` with the pattern or identifier:

```lean
let coreContext : Core.Context :=
  { fileName := inputContext.fileName, fileMap := inputContext.fileMap }
```

These separator rules are structural rather than renderer spelling checks. A
rule simply does not offer a break before its separator.

## File-level whitespace

These rules apply to every formatted file:

- CRLF and CR line endings become LF.
- Trailing spaces and tabs are removed.
- A run of blank lines becomes at most one blank line.
- A nonempty file ends with exactly one newline.
- Empty formatted output remains empty.

## Ignored Regions

Use `-- leanfmt: off next` before syntax to preserve the next complete syntax
node exactly:

```lean
-- leanfmt: off next
def handAligned   :   Nat:=
       1
```

The marker attaches to the next parsed Lean syntax node, not the next indentation
block. At the top level, it preserves the complete command. Within a declaration,
it can preserve a nested term such as a manually aligned function body:

```lean
def handAlignedFunction : Nat → Nat :=
  -- leanfmt: off next
  fun n =>
      n + 1
```

Use `-- leanfmt: off` and `-- leanfmt: on` on their own line-comment lines to
preserve a manual source region exactly:

```lean
def formattedBefore:Nat:=0

-- leanfmt: off
def handAligned   :   Nat:=
       1
-- leanfmt: on

def formattedAfter:Nat:=2
```

LeanFmt formats the parseable chunks before and after the region, then splices
the ignored marker lines and enclosed lines back unchanged. An `off` marker
without a matching `on` marker preserves the rest of the file.

## Comments

Line comments, block comments, nested block comments, and doc comments keep
their text. LeanFmt cleans surrounding whitespace and reindents comment trivia
when a containing construct moves.

```lean
-- module comment

/- block comment -/
def f : Nat :=
  -- body comment
  0
```

A trailing line comment stays on its line:

```lean
def answer : Nat := 0 -- trailing comment
```

Comment contents are not wrapped or rewritten. Module and declaration documentation
comments retain their exact internal whitespace and line shape.

## Token spacing

LeanFmt normally inserts one space between adjacent ordinary tokens and keeps
punctuation tight.

```lean
def identity : Nat → Nat :=
  fun x => x

def optionConstructor :=
  some .null
```

The main punctuation rules are:

- no space after `(`, `[`, `⟨`, `⟪`, `@`, or `@[`;
- no space before `)`, `]`, `⟩`, `⟫`, `,`, `;`, or `@`;
- dots stay tight in projections and qualified names;
- ordinary operators and declaration punctuation receive surrounding spaces;
- compact `!value` remains compact when `!` and the following token were
  adjacent; otherwise `! value` retains a space.

Braces retain the source's tight or spaced style where adjacency makes that
distinction safe:

```lean
{data := .null}
{ data := .null }
```

LeanFmt does not infer that whitespace before a dot is always removable. In
Lean, a dot after an expression can also begin an anonymous constructor, so the
syntax tree and original adjacency are respected.

Interpolated strings are single atoms. The `s!` prefix stays attached to the
string, and neither source breaks nor width wrapping introduce breaks inside an
interpolation:

```lean
s!"expected three operands, got {repr other}"
```

The containing application may break before the whole interpolated string.

## Modules and commands

Imports and top-level commands start on separate lines. Their order is
preserved. A `module` command, consecutive `public import` commands,
consecutive ordinary imports, and the following command form separate groups
with one blank line. Imports within one group have no blank lines between them.

```lean
module

public import Lean
public import Std

import Lean.Elab
import Lean.Parser

/-! # Example -/

namespace Example

def answer : Nat := 42

end Example
```

A module docstring is separated from the first declaration. Leading comments
and declaration docstrings stay attached to the command they describe.

Multiline top-level declarations have a blank line between them and adjacent
declarations. Short one-line declarations may remain grouped without blank
lines:

```lean
structure Point where
  x : Nat
  y : Nat

def origin := Point.mk 0 0
def unitX := Point.mk 1 0

structure Segment where
  start : Point
  stop : Point
```

Existing blank lines may still separate short declaration groups and other
top-level commands.

A long individual import is not split internally. Syntax declarations and
other command forms keep their tokens and use either an explicit command rule
or the generic structural layout.

```lean
import Very.Long.Module.Name.ThatRemainsOneImportCommand

syntax "widget" : term
```

Lake package commands keep `where` on the header and indent configuration fields one
level. A multiline Git dependency breaks after `git`, and its revision separator keeps
ordinary source spacing:

```lean
package example where
  srcDir := "."

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.32.0"
```

An attribute may share the line of any top-level command that accepts declaration
attributes when the source keeps them together and the complete command fits on
that line. This applies equally to built-in declarations and commands added by
syntax extensions:

```lean
@[simp] theorem eraseP_nil : [].eraseP p = [] := rfl
```

A source break between an attribute and its command is preserved. A multiline
command breaks after the attribute before trying breaks inside the command:

```lean
@[ext]
structure Point where
  x : Nat
```

For example, a declaration that wraps because of width moves below its attribute:

```lean
@[simp]
theorem theoremNameWithEnoughCharactersToRequireAnAttributeHeaderBreak
    (value : VeryLongInputTypeName)
    : VeryLongOutputTypeName := proof
```

Keyword modifiers remain on the declaration header:

```lean
private theorem helper : True := by
  trivial
```

Continuation indentation is measured from the beginning of the command line,
not from the declaration keyword after its modifiers:

```lean
private inductive Aligned : List α -> Prop where
  | nil : Aligned []
  | cons : Aligned values -> Aligned (value :: values)
```

## Declaration headers

### Parameters

Declaration parameters flow at binder boundaries. LeanFmt keeps as many
binders as fit and places later binders on continuation lines indented four
spaces from the declaration base.

```lean
def lookupObject (schema : Schema) (typeName : Name)
    (fallback : ObjectType) : Option ObjectType :=
  body
```

Existing parameter breaks can be retained after the header no longer fits.

```lean
def shapeExample (arg1 : VeryLongTypeNameUsedForLayout)
    (arg2 : AnotherVeryLongTypeNameUsedForLayout)
    : VeryLongReturnInputTypeWithEnoughCharactersForLayoutTesting
      -> VeryLongReturnOutputTypeWithEnoughCharactersForLayoutTesting :=
  body
```
Grouping inside a binder remains logically intact, such as `(x y : Nat)` and
`{ObjectRef : Type}`. A long sequence of names may wrap within the same pair of
delimiters; it is not rewritten into separate binders.

```lean
def compareSelections
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      leftCurrentSelectionSet rightCurrentSelectionSet
      : List Selection) :=
  body
```

If one binder is too long, it may break before its type annotation:

```lean
def example
    (hknown
      : ∀ name value,
          predicate name value) :=
  body
```

### Return types

When a declaration header is too long, the return type moves to a line beginning
with `:`. This line uses the declaration continuation indentation rather than
the body indentation.

```lean
def lookupVariableValue? (variableValues : VariableValues) (name : Name)
    : Option InputValue :=
  body
```

Long function return types break before arrows:

```lean
def nestedReturnChain
    : A -> VeryLongIntermediateReturnTypeWithEnoughCharactersForLayoutTesting
      -> VeryLongFinalReturnTypeWithEnoughCharactersForLayoutTesting :=
  body
```

Return-type arrow chains use flow layout: only the boundaries required to fit
the line are broken.

### Definition bodies

A body that does not fit on the header starts after `:=` and is indented one
level:

```lean
def wrappedApplicationArgument : Result :=
  singleFieldResult responseName
    (completeValue schema resolvers variableValues
      fuel' fieldDefinition.outputType
      (field :: fields) resolved)
```

An existing break immediately after `:=` is an accepted source break, even when
the body itself would fit on the header. This allows a project to retain a
deliberately multiline definition style.

Bodies beginning with `do` or `by` keep that keyword attached to `:=`; the
nested construct owns its body layout.

```lean
def lookupObject (schema : Schema) (typeName : Name) : Option ObjectType := do
  body
```

### `where` blocks

`where` returns to the declaration's base column. Nested declarations are
indented one level.

```lean
def outer : Nat :=
  inner
where
  inner : Nat := 0
```

Termination clauses follow the same ownership rule. `termination_by` and
`decreasing_by` return to the base column of the declaration they modify. A
termination measure may wrap one level beneath its keyword. The tactic after
`decreasing_by` retains its source layout, rebased beneath the formatted clause.

```lean
def outer (n : Nat) : Nat :=
  helper n
termination_by n
decreasing_by
  exact outerProof
where
  helper (n : Nat) : Nat := helper (n - 1)
  termination_by n
  decreasing_by
    exact helperProof
```

### Theorems and proofs

Theorem headers use the same parameter and return-type rules as definitions.
In a simple theorem, `:= by` remains on the final header line:

```lean
theorem theoremArrowChain (h : HypothesisWithEnoughCharactersForLayoutTesting)
    : FirstCondition -> SecondCondition -> FinalCondition := by
  exact proof
```

The source text of theorem proof values is preserved. Definitions and
abbreviations containing proof subtrees are preserved as a whole. The tactic
body after `decreasing_by` is protected separately from the formatted
termination-clause keywords and measure. LeanFmt can therefore format
surrounding declarations and propositions without imposing a tactic style.

Equation-style theorem and definition arms begin on their own lines and use the
declaration body indentation.

```lean
theorem equations : List Nat -> True
  | [] => by
      trivial
  | _ :: rest => by
      trivial
```

## Structures, inductives, and mutual declarations

Structure fields start on separate lines under `where`:

```lean
structure Point where
  x : Nat
  y : Nat
```

The field break does not force a fitting `extends` clause onto a continuation
line:

```lean
structure Candidate extends CandidateKey where
  occurrenceCount : Nat
```

Long field types use the same binder/type continuation principles as other
declarations.

```lean
structure ResolverFixture where
  resolve
    : Name -> Name -> List Argument
      -> Option ResponseValue
```

Inductive constructors also start on separate lines:

```lean
inductive Color where
  | red
  | green
  | blue
```

Constructor parameters flow at binder boundaries. A long constructor result
type moves to a leading `:` continuation line.

```lean
inductive ConstructorResultLayout where
  | intro (fields : List Field)
    : ConstructorResultLayoutForInput schema (ConstructorValue.object fields)
        (TypeRef.named typeName)
```

The arm base remains stable while long constructor binders flow beneath it:

```lean
inductive ConstructorBinderLayout where
  | intro (first : FirstTypeWithEnoughCharactersForLayoutTesting)
    (second : SecondTypeWithEnoughCharactersForLayoutTesting)
    : Result
```

This is the same base/flow relationship used by equation arms: `|` owns the
arm base, while binders and patterns own continuation opportunities.

`deriving` begins on its own line when it follows a multiline structure or
inductive declaration:

```lean
structure Response where
  data : Nat
  errors : Nat := 0
deriving Repr
```

Mutual declaration bodies are indented beneath `mutual`, and `end` returns to
the `mutual` column:

```lean
mutual
  def first : Nat := second
  def second : Nat := first
end
```

## Function applications

Applications use flow layout. The function and the longest fitting prefix of
arguments remain on the current line; later arguments wrap with one additional
indentation level.

```lean
veryLongFunctionName child children additionalArgumentOne
  additionalArgumentTwo additionalArgumentThree
```

Nested applications choose their continuation from the nested application's
structural base rather than aligning every line under the first argument:

```lean
singleFieldResult responseName
  (completeValue schema resolvers variableValues
    fuel' fieldDefinition.outputType
    (field :: fields) resolved)
```

If the flat application overflows, valid argument-boundary breaks from the
source are tried before automatic flow wrapping. Original indentation is
ignored and recomputed.

An argument whose formatted shape spans multiple lines is treated as not
fitting on the current line. The application therefore breaks before that
argument, including structured arguments such as `let`, `if`, `match`, and
structure instances. No special-case preference between parent and child
breaks is needed.

Projection chains do not break before a dot. The application around a
projection may still wrap:

```lean
def postfixProjection (schema : Schema) (typeName objectName : Name) :=
  (schema.getPossibleTypes typeName).contains objectName
```

## Unary prefix operators

A unary prefix operator stays on the first line of its operand. If the operand
is a long application, the application wraps at its own argument boundaries;
the formatter does not leave the prefix on a line by itself.

```lean
theorem duplicateArgumentNamesRejected
    : ¬ GraphQL.Validation.argumentsValid sampleSchema
          [testEpisodeArgumentDefinition] [] duplicateEpisodeArguments := by
  exact proof
```

This applies consistently to logical negation `¬`, compact bang `!`, numeric
negation `-`, and bitwise complement `~~~`. Postfix operators follow their own
right-attached layout.

## Tail indentation

LeanFmt breaks before an infix operator so the operator visually connects the
lines in its chain:

```lean
  f argumentOne argumentTwo
  + g argumentOne argumentTwo
  + h argumentOne argumentTwo
```

Consecutive operators of the same parser kind are formatted as one chain. The
same leading-operator layout applies inside an indented declaration body:

```lean
def equality : Prop :=
  veryLongLeftHandSideExpressionWithEnoughCharactersForLayoutTesting
  = veryLongRightHandSideExpressionWithEnoughCharactersForLayoutTesting
```

A multiline operand needs a visible local hierarchy. A match keeps its normal
internal arm indentation, but the whole block moves inward when it is the
non-final operand of an infix expression:

```lean
  match value with
    | first => firstResult
    | second => secondResult
  + other
```

The formatter describes this with a segment's **head indentation** and **tail
indentation**:

- A segment starts at a physical column. Its head indentation is the nearest
  indentation column at or after that start column.
- Its tail indentation is the minimum indentation for later lines when the
  segment becomes multiline.
- A non-final infix operand lifts its tail one level beyond the following
  operator. Other infix-like syntax and flow layout use the same principle.

When a segment begins between indentation columns, its head rounds up. This
keeps a nested block clear of the following operator:

```lean
  -> match value with
        | first => firstResult
        | second => secondResult
      ∧ other
```

Tail indentation is a floor, not an amount added to every rule indentation. An
application already asks for one continuation level, so a tail at that level
does not push it farther:

```lean
  someFunction firstLongArgument
    nextArgument
  + g
```

The floor accumulates through nested non-final operands. This makes each inner
operator deeper than the operator containing it, while the application keeps
its own continuation relationship:

```lean
  someFunction firstLongArgument
      nextArgument
    + g
  :: h
```

In real code, an application inside `::`, itself inside `++`, follows the same
hierarchy:

```lean
  (Selection.field responseName fieldName arguments fieldDirectives
        fieldSelectionSet
      :: inlineSelectionSet
    ++ rest)
```

Some constructs have several relative indentation levels. A multiline
structure places fields one level inside its braces while its closing brace
returns to the brace level:

```lean
something
+ {
    field1 := value1,
    field2 := value2
  }
  - g
```

When tail indentation raises such a construct, LeanFmt shifts the complete
break profile together. It does not independently clamp every line, because
that would flatten the difference between fields and the closing brace:

```lean
-> {
      field1 := value1,
      field2 := value2
    }
    :: g
```

Parentheses stay tight around their expression, and the expression inside owns
the breaks. When a parenthesized chain is a non-final operand, its operators
remain one level deeper than the surrounding chain:

```lean
((executableFieldSelections [first]
    ++ middle
    ++ executableFieldSelections [later])
  ++ suffix)
```

## Propositions and arrows

LeanFmt distinguishes the layout role of arrow chains from their syntactic
context:

- arrows in ordinary function types flow and wrap only where required;
- arrows in theorem statements, `Prop` definition bodies, quantifier bodies,
  and logical operands break as a balanced logical group.

```lean
theorem valid
    : FirstCondition
      -> SecondCondition
      -> FinalCondition := by
  exact proof
```

Logical and equality operators recognized for balanced proposition layout are
`->`, `→`, `∧`, `∨`, `/\`, `\/`, and `=`. A lower-precedence outer connector
breaks before nested higher-precedence expressions.

```lean
def leadingEqualityAndOperand : Prop :=
  firstCondition = secondConditionWithEnoughCharactersForLayoutTesting
  ∧ thirdConditionWithEnoughCharactersForLayoutTesting
  ∧ finalConditionWithEnoughCharactersForLayoutTesting
```

`≠` receives normal spacing but is not included in the balanced logical group.

Nested disjunction and conjunction groups retain a visible local hierarchy:

```lean
def parenthesizedDisjunctionChain (schema : Schema) (implementation expected : Name)
    : Prop :=
  (schema.isLeafType implementation
    ∧ schema.isLeafType expected
    ∧ implementation = expected)
  ∨ (schema.isCompositeType implementation
      ∧ schema.isCompositeType expected
      ∧ ∀ objectName,
          schema.typeIncludesObject implementation objectName
          -> schema.typeIncludesObject expected objectName)
```

## Quantifiers and lambdas

A quantifier stays flat when it fits. Otherwise its body begins after the comma
and is indented one level.

```lean
def mixedAdjacentQuantifiers : Prop :=
  ∃ objectType,
    ∀ typeCondition,
      typeCondition ∈ typeConditions
      -> objectType ∈ schema.getPossibleTypes typeCondition
```

Adjacent quantifiers of the same kind do not add another indentation level
between them:

```lean
def adjacentQuantifiers : Prop :=
  ∀ x, ∀ y, body x y
```

Different quantifiers add a level when their bodies wrap:

```lean
def mixedAdjacentQuantifiers : Prop :=
  ∃ objectType,
    ∀ typeCondition,
      predicate objectType typeCondition
```

Long binder sequences can flow between binders and between names belonging to
one untyped binder sequence.

```lean
∃ leftPrefixFields leftPrefixErrors rightPrefixFields rightPrefixErrors
    leftSuffixFields leftSuffixErrors rightSuffixFields rightSuffixErrors,
  predicate
```

Source breaks between fitting adjacent quantifiers are not preserved merely
because they appeared in the input.

A lambda breaks after `=>` and indents its body one level:

```lean
fun objectType =>
  normalizeSelectionSet schema objectType selections
```

## `let` expressions

A `let` body always begins on a separate line. A long right-hand side begins
after `:=` with one additional indentation level:

```lean
def withLet : Result :=
  let normalizedSubselections :=
    normalizeSelectionSet schema returnType mergedSubselections
  normalizedSubselections
```

The body aligns with `let`, not with the right-hand side. When a `let` appears
after a leading operator, LeanFmt may insert alignment space before `let` so the
result also satisfies Lean's indentation-sensitive parser.

For a layout-delimited `let`, Lean must be able to tell where the right-hand
side ends and the body begins. When the body starts with syntax that could also
be another function argument, LeanFmt aligns `let` to an indentation column.
This may retain a space after an opening parenthesis:

```lean
result
  = ( let matching :=
        computeMatchingSelections schema responseName selections
      useMatchingSelections matching)
```

When the leading syntax cannot continue a function application, the body
boundary is already unambiguous and the opening parenthesis remains tight.
Examples include bodies starting with `match`, `if`, `let`, or `by`:

```lean
result
  = (let collectedRest :=
        collectRest selections
      match lookupField fieldName with
      | none => collectedRest
      | some field => field :: collectedRest)
```

LeanFmt asks Lean's active term parser this question at function-argument
precedence. Syntax extensions declared or imported by a project therefore
follow their own declared precedence instead of a built-in keyword list.

An explicitly semicolon-delimited `let` does not depend on indentation for this
boundary and keeps tight parenthesis spacing.

A structured right-hand side keeps its own layout below `:=`:

```lean
def letMatchRhs : Result :=
  let current :=
    match selection with
    | .field responseName fieldName => collectField responseName fieldName
    | .inlineFragment selectionSet => collectFields selectionSet
  current
```

Monadic bindings follow the same header/RHS split. Both identifier and pattern
bindings keep `←` on the header and break after it when necessary:

```lean
let (normalizedSource, normalizeMs) ←
  timeIO <| pure <| normalize source
```

A `suffices` body likewise begins on a separate line after the proposition and
its `from` proof. The body remains offside from the proof expression so Lean's
layout parser cannot absorb it into that expression.

A `have` body also begins on a separate line. When its declaration does not fit,
the assigned value breaks after `:=` while the following body remains aligned
with the `have` expression rather than the assigned value.

## Conditionals

A fitting conditional stays on one line. A multiline conditional breaks as a
balanced branch structure:

```lean
if responseName == group.fst then
  (responseName, fields ++ group.snd) :: rest
else
  (responseName, fields) :: addExecutableGroup group rest
```

An `else if` keeps the nested `if` on the `else` line rather than adding an
extra branch indentation. The complete chain is one balanced structure: if one
branch boundary breaks, every `then` branch and the final `else` branch break
together.

```lean
if firstCondition then
  firstResult
else if secondCondition then
  secondResult
else
  finalResult
```

Accepted source breaks between branch boundaries can keep an intentional
multiline conditional even when a flatter form fits. Because conditionals are
non-flow rules, any accepted branch break activates the complete balanced
branch layout.

Conditionals normally start on an indentation boundary. An immediately preceding
opening parenthesis keeps tight spacing instead; branch indentation rounds up from
the off-column `if`. This exception affects only the first line:

```lean
pure
  (if firstCheck && secondCheck && thirdCheck && fourthCheck then
      0
    else
      1)
```

Thus an input that breaks only before `else` does not remain half-broken:

```lean
if arg.startsWith "-" then
  .error s!"unknown option: {arg}"
else
  loop options (FilePath.mk arg :: files) rest
```

## Match expressions and equation arms

Match alternatives start on their own lines and align with the `match` keyword:

```lean
match variableValues with
| [] => none
| (variableName, value) :: rest =>
    if variableName = name then some value else lookupVariableValue? rest name
```

A long discriminant is formatted by its own rules before `with`:

```lean
match veryLongFunctionName child children additionalArgumentOne
        additionalArgumentTwo with
| [] => 0
| _ :: rest => rest.length
```

Multiple match discriminants are grouped as peers. They use flow layout with
breaks after commas, aligned under the first discriminant following `match`, so
only the suffix that does not fit moves:

```lean
match defaultPresentChildIndexBefore? segment index,
      defaultPresentChildIndexAfter? segment index,
      defaultPresentChildIndexAround? segment index with
| some before,
  some after,
  some around => result
```

Multiple patterns in one arm are balanced peers. If a pattern boundary breaks,
all comma-separated pattern boundaries break together. A long right-hand side
breaks after `=>` and is indented two levels from the arm start:

```lean
| .field responseName fieldName arguments directives selectionSet =>
    collectFields schema responseName fieldName arguments directives selectionSet
```

Pattern lists also flow when they become too long:

```lean
| parentType,
  _source,
  .field responseName fieldName arguments directives selectionSet =>
    body
```

Short right-hand sides stay on the arrow line. A `by` or `do` right-hand side
also stays attached to `=>`, and its nested body owns subsequent breaks.

```lean
| .some value => do
    process value
| .none => by
    exact defaultValue
```

Equation-style declaration arms follow the same alternative layout.

Alternative patterns are grouped as peers before rendering, like operands in
an infix chain. This lets multiple `|` patterns wrap in a balanced layout at
the arm base instead of inheriting accidental nesting from the raw parser
tree. A pattern alias such as `fieldSelection@(` stays attached; if its nested
pattern must wrap, the break occurs inside the parentheses before the arm's
`=>` body layout is considered.

Indentation is relative to the arm's logical base, even when the enclosing
expression starts at a shifted physical column. The formatter does not align
continuations under an incidental token column. Comments between a pattern,
separator, and body remain attached to their source tokens and are reindented
with the resulting arm rather than changing which rule wins.

## `do` expressions

`do` remains attached to the expression that introduces it, and statements
start one level below it:

```lean
def run : IO Unit := do
  IO.println "start"
  IO.println "done"
```

Statement boundaries are structural and remain on separate lines.

A semicolon explicitly joins adjacent statements. If the complete sequence
fits, it may remain on one line even when the source broke after `;`:

```lean
IO.println usage; pure 0
```

If it does not fit, the do-sequence rules provide the normal balanced
statement boundaries.

A refutable `let` with a fallback treats its value and fallback as separate
branches. A multiline value begins one level below `:=`; `|` aligns with
`let`, as required by Lean's layout parser:

```lean
let .some value :=
  lookupVeryLongValue firstArgument secondArgument thirdArgument
| return none
consume value
```

If only the fallback is long, the value can remain on the header while the
break occurs before `|`:

```lean
let .some value := candidate
| recoverVeryLongValue firstArgument secondArgument thirdArgument
consume value
```

The successful continuation also aligns with `let`. Formatting inside the
value and fallback remains the responsibility of their own expression rules.

## Subtypes

A subtype stays compact when it fits:

```lean
{ target : ScopedField // target ∈ fields }
```

When it does not fit, it breaks before `//`:

```lean
{ targetField : ScopedFieldVeryLongTypeNameLikeThis
  // targetField ∈ targetFieldsWithVeryLongName }
```

The property can then use ordinary proposition layout.

## Arrays, tuples, anonymous constructors, and structure instances

Single-line collections remain compact:

```lean
[firstItem, secondItem, thirdItem]
(firstValue, secondValue)
{ data := .null, errors := 1 }
```

Multi-item arrays, tuples, and anonymous constructors use balanced layout: when
the collection does not fit, the opening boundary, every item boundary, and the
closing delimiter break together.

```lean
[
  veryLongFirstArrayItemNameUsedForLayoutTesting,
  veryLongSecondArrayItemNameUsedForLayoutTesting,
  veryLongThirdArrayItemNameUsedForLayoutTesting
]
```

LeanFmt does not add a trailing comma.

A single multiline item keeps the outer array compact around that item. This
supports common nested forms such as an array containing one structure value:

```lean
[{
  parentType := parentType,
  responseName := responseName,
  fieldName := fieldName
}]
```

Structure instances with several fields break after `{`, between fields, and
before `}`. Comma-separated fields remain flat when they fit. Newline-separated
fields without commas are structurally multiline because Lean's layout syntax
requires those boundaries.

Multiple sources in a structure update align as peers before the `with` suffix:

```lean
{
  firstParent,
  secondParent with
    field := value
}
```

The opening and closing brace breaks are balanced. A type ascription following a
multiline structure keeps `:` with its type:

```lean
response
  = ({
        data := ResponseValue.object fields,
        errors := errors
      }
      : Response)
```

A fitting constructor remains completely flat, including a nested constructor
used as a field value. If a constructor argument is too wide, its containing
application breaks before `{`. In a declaration body, the declaration first
uses its normal break after `:=`; only then does the constructor apply its own
field breaks. This avoids splitting a short constructor merely because the
source happened to break inside it.

```lean
def recordOperand :=
  {
    parentType := validParentWithEnoughCharactersForLayoutTesting,
    responseName := responseNameWithEnoughCharactersForLayoutTesting
  }
```

A multiline tuple uses the same balanced opening, item, and closing shape:

```lean
def tupleOperand :=
  (
    firstItemNameWithEnoughCharactersForLayoutTesting,
    secondItemNameWithEnoughCharactersForLayoutTesting,
  )
```

Existing punctuation is preserved, so the trailing comma above remains because
it was present in the source; LeanFmt does not add one.

Anonymous constructors use the same balanced shape. Single-field constructors
remain flat when they fit.

```lean
def setoidWitness :=
  ⟨
    fun a b => related a b,
    fun a => ⟨refl a⟩,
    fun h => h.symm,
    fun h₁ h₂ => h₁.trans h₂
  ⟩
```

Structure updates follow the same field layout:

```lean
def normalizeOperation (schema : Schema) (operation : Operation) : Operation :=
  {
    operation with
      selectionSet :=
        normalizeSelectionSet schema operation.rootType operation.selectionSet
  }
```

The update source is one level inside the braces, and fields are one level
inside the `with` header. A short update remains flat, such as
`{ operation with selectionSet := selectionSet }`.

## Unknown and custom syntax

Every parser token remains present even when LeanFmt has no explicit rule for a
syntax node. The generic rule examines only the node's immediate child shape:

- a token between two child nodes is treated as an infix-like break point;
- otherwise, boundaries between present children become flow break points;
- token spelling is not used to guess the meaning of the syntax.

This provides conservative wrapping for long custom syntax without pretending
to understand it. Formatting developers can use `--check-exception` to identify
syntax that deserves an explicit rule.

Unknown syntax is lossless, but its whitespace is not guaranteed to remain
byte-for-byte unchanged. Multiline custom braced term syntax is a conservative
exception: LeanFmt keeps its source layout instead of canonicalizing indentation for
an extension-owned DSL.

A short custom syntax declaration can remain flat:

```lean
syntax "widget" : term
```

If a larger custom node overflows, its parser-child boundaries determine the
generic wrapping until LeanFmt has a dedicated rule for that syntax.

## Diagnostics

Diagnostics observe source without changing formatting behavior. The compact
bang diagnostic reports `!f a b` because it can be read as either compact
negation or a function application.

These spellings are accepted and preserved:

```lean
!value
! value
! f a b
! (f a b)
```

The ambiguous `!f a b` spelling is reported but not automatically rewritten.

## Formatting guarantees

LeanFmt is designed around these checks:

1. Parsing succeeds with Lean's parser and active syntax extensions.
2. Reconstructing the syntax tree reproduces the parsed source.
3. Formatting preserves the code-token sequence and the exact text inside comments;
   whitespace between code and comment fragments is normalized for comparison.
4. Formatting is idempotent: formatting the output again produces the same
   output.

The third and fourth properties are available as internal CLI checks for
formatter development. They describe formatter correctness, not style options
that ordinary users need to select.

Formatting may require more than one parse/render pass because a first layout
can expose a different accepted source-break shape to the next pass. LeanFmt
iterates to a fixed point with a hard limit of four passes. If an intermediate
result does not parse, repeats a previously seen result, or does not converge
within that limit, LeanFmt emits a warning and returns the original source
rather than treating the fallback as a hard formatter error.
