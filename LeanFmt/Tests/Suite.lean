import LeanFmt
import LeanFmt.Cli
import LeanFmt.Tests.Cli
import LeanFmt.Tests.ProjectSyntax

open System

namespace LeanFmt.Tests

def assertEq (label expected actual : String) : IO Unit := do
  unless actual == expected do
    throw <| IO.userError s!"{label} mismatch\nexpected:\n{expected}\nactual:\n{actual}"

def assertTrue (label : String) (value : Bool) : IO Unit := do
  unless value do
    throw <| IO.userError s!"assertion failed: {label}"

def textContains (text needle : String) : Bool :=
  match text.splitOn needle with
  | [_] => false
  | _ => true

def assertTextContains (label text needle : String) : IO Unit := do
  assertTrue label (textContains text needle)

def assertTextLacks (label text needle : String) : IO Unit := do
  assertTrue label (!textContains text needle)

def codePreservedIgnoringWhitespace (env : Lean.Environment) (before after : String)
    : IO Bool := do
  let beforeModule ←
    SyntaxTree.parseModuleStringWithEnv env before "preservation-before.lean"
  let afterModule ←
    SyntaxTree.parseModuleStringWithEnv env after "preservation-after.lean"
  pure <| Formatter.Diagnostics.preservesCodeIgnoringWhitespace beforeModule afterModule

def assertSyntaxTreeRoundTrip (env : Lean.Environment) : IO Unit := do
  let source := "def f (x : Nat) :=\n" ++ "  x + 1\n"
  let moduleTree ←
    SyntaxTree.parseModuleStringWithEnv env source "syntax-tree-round-trip.lean"
  assertEq "syntax tree reconstruction" source moduleTree.reconstruct

def assertSyntaxTreeWhereRoundTrip (env : Lean.Environment) : IO Unit := do
  let source :=
    "def outer : Nat :=\n" ++ "  inner\n" ++ "where\n" ++ "  inner : Nat := 0\n"
  let moduleTree ←
    SyntaxTree.parseModuleStringWithEnv env source "syntax-tree-where.lean"
  assertEq "syntax tree where reconstruction" source moduleTree.reconstruct

def assertPreservationDetectsSyntaxChange (env : Lean.Environment) : IO Unit := do
  let source :=
    "def letAlt (x? : Option Nat) : Nat := do\n"
    ++ "  let .some x ← x? | return 0\n"
    ++ "  x\n"
  let changed :=
    "def letAlt (x? : Option Nat) : Nat := do\n" ++ "  let .some x ← x? | return 0 x\n"
  assertTrue "preservation rejects syntax-significant whitespace changes"
    (!(← codePreservedIgnoringWhitespace env source changed))

def assertOverlappingQuotationTokensRemoved (env : Lean.Environment) : IO Unit := do
  let source :=
    "syntax \"field \" str \"{\" term,* \"}\" : term\n"
    ++ "macro_rules\n"
    ++ "  | `(field $name:str { $selection,* }) =>\n"
    ++ "      `(Selection.field $name [$selection,*])\n"
  let moduleTree ←
    SyntaxTree.parseModuleStringWithEnv env source "quotation-overlap.lean"
  assertEq "quotation overlap syntax tree reconstruction" source moduleTree.reconstruct
  let formatted ← Formatter.formatSourceWithEnv env source "quotation-overlap.lean"
  assertTrue "quotation formatting preserves non-whitespace"
    (← codePreservedIgnoringWhitespace env source formatted)
  assertTextContains "quotation splice spacing is preserved"
    formatted "`(field $name:str { $selection,* })"
  assertTextLacks "quotation splice is not duplicated"
    formatted "{ $selection,* } { $selection,* }"

def assertTacticQuotationAntiquotationPreserved (env : Lean.Environment) : IO Unit := do
  let source :=
    "macro \"finish_true_with_antiquotation\" : tactic =>\n"
    ++ "  `(tactic|\n"
    ++ "    first | exact $(Lean.mkIdent `True.intro):term | exact $(Lean.mkIdent `True.intro):term)\n"
  let result ←
    Formatter.formatSourceWithEnvDetailed env source
      "tactic-quotation-antiquotation.lean"
  assertTrue "tactic quotation antiquotation does not fall back" (!result.fellBack)
  assertTrue "tactic quotation antiquotation preserves code"
    (← codePreservedIgnoringWhitespace env source result.formatted)
  assertTextContains "tactic quotation antiquotation prefix stays tight"
    result.formatted "$(Lean.mkIdent `True.intro):term"
  assertTextLacks "tactic quotation antiquotation prefix is not split"
    result.formatted "$\n"

def assertOverlappingEmptySyntaxTokensRemoved (env : Lean.Environment) : IO Unit := do
  let source :=
    "syntax \"field \" str \"{\" term,* \"}\" : term\n" ++ "#check field \"empty\" {}\n"
  let moduleTree ←
    SyntaxTree.parseModuleStringWithEnv env source "empty-syntax-overlap.lean"
  assertEq "empty syntax overlap tree reconstruction" source moduleTree.reconstruct
  let formatted ← Formatter.formatSourceWithEnv env source "empty-syntax-overlap.lean"
  assertTrue "empty syntax formatting preserves non-whitespace"
    (← codePreservedIgnoringWhitespace env source formatted)
  assertTextLacks "empty syntax block is not duplicated" formatted "{} {}"
  let formattedAgain ←
    Formatter.formatSourceWithEnv env formatted "empty-syntax-overlap-formatted.lean"
  assertEq "empty syntax overlap formatting is parseable and idempotent"
    formatted formattedAgain

def assertSafeArrayIndexKeepsPostfixQuestion (env : Lean.Environment) : IO Unit := do
  let source :=
    "def safeArrayIndex (children : Array Nat) : Option Nat :=\n"
    ++ "  match children[0]? with\n"
    ++ "  | some child => some child\n"
    ++ "  | none => none\n"
  let formatted ← Formatter.formatSourceWithEnv env source "safe-array-index.lean"
  assertTextContains "safe array index keeps postfix question" formatted "children[0]?"
  let formattedAgain ←
    Formatter.formatSourceWithEnv env formatted "safe-array-index-formatted.lean"
  assertEq "safe array index formatting is idempotent" formatted formattedAgain

def assertPostfixSuperscriptSpacingPreservesParse (env : Lean.Environment)
    : IO Unit := do
  let source :=
    "def applyInverse {G : Type} [Inv G] (f : G -> G -> G) (m n : G) :=\n"
    ++ "  f m⁻¹ n\n"
  let formatted ← Formatter.formatSourceWithEnv env source "postfix-superscript.lean"
  assertTrue "postfix superscript formatting preserves code"
    (← codePreservedIgnoringWhitespace env source formatted)
  assertTextContains "postfix inverse stays attached" formatted "m⁻¹"
  assertTextLacks "postfix inverse is not split" formatted "m ⁻¹"
  let formattedAgain ←
    Formatter.formatSourceWithEnv env formatted "postfix-superscript-formatted.lean"
  assertEq "postfix superscript formatting is idempotent" formatted formattedAgain

def assertBlockCommentInternalWhitespacePreservedByFormatting (env : Lean.Environment)
    : IO Unit := do
  let comment := "/-\n" ++ "Copyright line\n"
  let comment := comment ++ "  Indented author line keeps spacing\n" ++ "-/\n"
  let source := comment ++ "def commentAfterHeader := 0\n"
  let formatted ← Formatter.formatSourceWithEnv env source "block-comment-spacing.lean"
  assertTrue "block comment formatting preserves code"
    (← codePreservedIgnoringWhitespace env source formatted)
  assertTextContains "block comment indentation is preserved" formatted
    "  Indented author line keeps spacing"

def assertModuleDocInternalBlankLinesPreservedByFormatting (env : Lean.Environment)
    : IO Unit := do
  let source := "/-!\nA\n\n\nB\n-/\n\ndef moduleDocBlankLines := 0\n"
  let formatted ← Formatter.formatSourceWithEnv env source "module-doc-blank-lines.lean"
  assertTrue "module doc blank lines preserve code"
    (← codePreservedIgnoringWhitespace env source formatted)
  assertTextContains "module doc internal blank line run is preserved"
    formatted "A\n\n\nB"

def syntheticAtomToken (lexeme : String) : SyntaxTree.Token :=
  SyntaxTree.tokenOfSynthetic .atom `token lexeme (String.Pos.Raw.mk 0)
    (String.Pos.Raw.mk 0)

def syntheticAtomTokenAt (lexeme : String) (start stop : Nat) : SyntaxTree.Token :=
  SyntaxTree.tokenOfSynthetic .atom `token lexeme (String.Pos.Raw.mk start)
    (String.Pos.Raw.mk stop)

def assertCustomNotationBracketSpacing : IO Unit := do
  assertEq "custom notation open bracket keeps tight spacing" ""
    (Formatter.SpaceRules.interTokenWhitespace ""
      (syntheticAtomToken "→ₗ[") (syntheticAtomToken "R"))
  assertEq "custom equivalence notation bracket keeps tight spacing" ""
    (Formatter.SpaceRules.interTokenWhitespace ""
      (syntheticAtomToken "≃ₗ[") (syntheticAtomToken "R"))
  assertEq "strict implicit binder open keeps tight spacing" ""
    (Formatter.SpaceRules.interTokenWhitespace ""
      (syntheticAtomToken "⦃") (syntheticAtomToken "a"))
  assertEq "strict implicit binder close keeps tight spacing" ""
    (Formatter.SpaceRules.interTokenWhitespace ""
      (syntheticAtomToken "a") (syntheticAtomToken "⦄"))
  assertEq "dot identifier stays tight" ""
    (Formatter.SpaceRules.spaceBetweenTokens
      (syntheticAtomToken ".") (syntheticAtomToken "inr"))
  assertEq "qualified identifier dot stays tight" ""
    (Formatter.SpaceRules.spaceBetweenTokens
      (syntheticAtomToken "Nat.") (syntheticAtomToken "succ"))
  assertEq "operator ending in dot keeps right spacing" " "
    (Formatter.SpaceRules.spaceBetweenTokens
      (syntheticAtomToken "→.") (syntheticAtomToken "List"))
  assertEq "pattern ellipsis does not attach to arrow" " "
    (Formatter.SpaceRules.spaceBetweenTokens
      (syntheticAtomToken "..") (syntheticAtomToken "=>"))
  assertEq "source space before explicit identifier marker is preserved" " "
    (Formatter.SpaceRules.interTokenWhitespace "f @x"
      (syntheticAtomTokenAt "f" 0 1) (syntheticAtomTokenAt "@" 2 3))
  assertEq "true postfix superscript marker stays tight" ""
    (Formatter.SpaceRules.spaceBetweenTokens
      (syntheticAtomToken "m") (syntheticAtomToken "⁻¹"))
  assertEq "operator-like modifier token gets ordinary spacing" " "
    (Formatter.SpaceRules.spaceBetweenTokens
      (syntheticAtomToken "vec") (syntheticAtomToken "ᵥ*"))

def assertOperatorLikeModifierTokenPreservesParse (env : Lean.Environment)
    : IO Unit := do
  let source :=
    "def vecMul (left right : Nat) := left + right\n"
    ++ "infixl:70 \" ᵥ* \" => vecMul\n"
    ++ "def value := 1 ᵥ* 2\n"
  let formatted ← Formatter.formatSourceWithEnv env source "operator-like-modifier.lean"
  assertTrue "operator-like modifier token formatting preserves code"
    (← codePreservedIgnoringWhitespace env source formatted)
  assertTextContains "operator-like modifier token keeps left boundary"
    formatted "1 ᵥ* 2"
  assertTextLacks "operator-like modifier token does not attach to left operand"
    formatted "1ᵥ*"

def assertSetOptionInBreaksAfterIn (env : Lean.Environment) : IO Unit := do
  let source :=
    "set_option backward.isDefEq.respectTransparency false in\n"
    ++ "theorem scopedOptionTheorem (veryLongArgumentNameForTheorem : Nat)\n"
    ++ "    : True := by\n"
    ++ "  trivial\n"
  let formatted ← Formatter.formatSourceWithEnv env source "set-option-in.lean"
  assertTrue "set_option in formatting preserves code"
    (← codePreservedIgnoringWhitespace env source formatted)
  assertTextContains "set_option keeps in before command break" formatted "false in\n"
  assertTextLacks "set_option does not break before in" formatted "false\nin theorem"

def assertCommandInWrapperPreservesBreakAfterIn (env : Lean.Environment) : IO Unit := do
  let source :=
    "variable {p q r s t u v w : Prop} in\n"
    ++ "theorem wrapperBreaksBeforeDeclaration\n"
    ++ "    : p ∧ q ∧ r ∧ s ∧ t ∧ u ∧ v ∧ w -> p := by\n"
    ++ "  intro h\n"
    ++ "  exact h.1\n"
  let formatted ← Formatter.formatSourceWithEnv env source "command-in-wrapper.lean"
  assertTrue "command in wrapper formatting preserves code"
    (← codePreservedIgnoringWhitespace env source formatted)
  assertTextContains "command in wrapper keeps command break after in"
    formatted "variable {p q r s t u v w : Prop} in\ntheorem"

def assertLeadingDotPatternConstructorsStayTight (env : Lean.Environment)
    : IO Unit := do
  let source :=
    "inductive Side where\n"
    ++ "  | inl\n"
    ++ "  | inr\n"
    ++ "\n"
    ++ "instance : DecidableRel (fun _ _ : Side => True)\n"
    ++ "  | .inl, .inr | .inr, .inl => isTrue trivial\n"
    ++ "  | .inl, .inl | .inr, .inr => isTrue trivial\n"
  let formatted ← Formatter.formatSourceWithEnv env source "leading-dot-patterns.lean"
  assertTrue "leading-dot pattern formatting preserves code"
    (← codePreservedIgnoringWhitespace env source formatted)
  assertTextLacks "leading-dot pattern constructor does not split after dot"
    formatted ".\n"
  assertTextLacks "leading-dot pattern constructor does not add space after dot"
    formatted ". inr"

def assertFormatterConvergencePassLimit : IO Unit := do
  assertTrue "formatter convergence pass limit"
    (Formatter.Internal.maxConvergencePasses == 4)

def assertFormatterFallbackResultIsObservable (env : Lean.Environment) : IO Unit := do
  let result ←
    Formatter.Internal.convergeSourceWithEnv env "def x := 1\n"
      "forced-format-fallback.lean" 0
  assertEq "formatter fallback returns original source" "def x := 1\n" result.formatted
  assertTrue "formatter fallback is observable" result.fellBack

def assertLayoutSensitiveTermsRemainParseableAndIdempotent (env : Lean.Environment)
    : IO Unit := do
  let source :=
    "def localRecursive (values : List Nat) : Nat :=\n"
    ++ "  let rec loop : List Nat -> Nat\n"
    ++ "    | [] => 0\n"
    ++ "    | _ :: rest => loop rest\n"
    ++ "  loop values\n"
    ++ "\n"
    ++ "def shiftedLocalRecursive (values : List Nat) : Nat :=\n"
    ++ "  abc (let rec loop : List Nat -> Nat\n"
    ++ "        | [] => 0\n"
    ++ "        | _ :: rest => loop rest\n"
    ++ "      loop values)\n"
    ++ "\n"
    ++ "def handled (action : IO Nat) : IO Nat := do\n"
    ++ "  try\n"
    ++ "    let value ← action\n"
    ++ "    pure value\n"
    ++ "  catch _ =>\n"
    ++ "    pure 0\n"
    ++ "\n"
    ++ "def controlFlow (values : List Nat) : IO Nat := do\n"
    ++ "  let mut total := 0\n"
    ++ "  for value in values do\n"
    ++ "    if value == 0 then\n"
    ++ "      total := total + 1\n"
    ++ "  pure total\n"
    ++ "\n"
    ++ "def branchLayout (first second : Bool) : IO Nat := do\n"
    ++ "  if first then\n"
    ++ "    pure 1\n"
    ++ "  else if second then\n"
    ++ "    IO.eprintln \"second\"\n"
    ++ "    pure 2\n"
    ++ "  else\n"
    ++ "    try\n"
    ++ "      pure 3\n"
    ++ "    catch _ =>\n"
    ++ "      IO.eprintln \"fallback\"\n"
    ++ "      pure 4\n"
  let formatted ← Formatter.formatSourceWithEnv env source "layout-sensitive-terms.lean"
  let _ ←
    SyntaxTree.parseModuleStringWithEnv env formatted "layout-sensitive-formatted.lean"
  let formattedAgain ←
    Formatter.formatSourceWithEnv env formatted "layout-sensitive-formatted.lean"
  assertEq "layout-sensitive terms remain idempotent" formatted formattedAgain
  assertTextContains "local recursive continuation keeps its layout"
    formatted "  loop values"
  assertTextContains "shifted local recursive continuation uses aligned local base"
    formatted "\n      loop values)"
  assertTextContains "multiline let argument breaks before the argument"
    formatted "  abc\n    ( let rec loop : List Nat -> Nat"
  assertTextContains "try catch keeps its layout" formatted "  catch _ =>"
  assertTextContains "do for keeps its layout" formatted "  for value in values do"
  assertTextContains "do if keeps its layout" formatted "    if value == 0 then"
  assertTextContains "else-if actions keep separate layout"
    formatted "  else if second then\n    IO.eprintln \"second\"\n    pure 2"
  assertTextContains "catch actions keep separate layout"
    formatted "    catch _ =>\n      IO.eprintln \"fallback\"\n      pure 4"

def assertGroupedApplication (env : Lean.Environment) : IO Unit := do
  let moduleTree ←
    SyntaxTree.parseModuleStringWithEnv env
      "def x := f a b\n" "grouped-application.lean"
  assertTrue "application node exists" (moduleTree.tree.containsNodeKind .application)
  match moduleTree.tree.firstNodeChildCount? .application with
  | some 3 => pure ()
  | other =>
      throw
      <| IO.userError
          s!"expected application to contain head plus two arguments, got {repr other}"

def assertGroupedInfixChain (env : Lean.Environment) : IO Unit := do
  let moduleTree ←
    SyntaxTree.parseModuleStringWithEnv env "def x := a + b + c\n" "grouped-infix.lean"
  match moduleTree.tree.firstInfixChainChildCount? `«term_+_» with
  | some 5 => pure ()
  | other =>
      throw
      <| IO.userError
          s!"expected infix chain to contain three operands and two operators, got {repr other}"

def assertHardWhitespaceFormatting (env : Lean.Environment) : IO Unit := do
  let source :=
    "def  f  (x  : Nat)  :=\r\n"
    ++ "  x   \r\n"
    ++ "\r\n"
    ++ "\r\n"
    ++ "def  g : Nat := 0   \r\n"
  let expected := "def f (x : Nat) :=\n" ++ "  x\n" ++ "\n" ++ "def g : Nat := 0\n"
  let formatted ← Formatter.formatSourceWithEnv env source "hard-whitespace.lean"
  assertEq "hard whitespace formatting" expected formatted

def assertImportsStayOnSeparateLines (env : Lean.Environment) : IO Unit := do
  let source :=
    "import GraphQL.Execution\n"
    ++ "import GraphQL.SchemaWellFormedness\n"
    ++ "import GraphQL.Validation\n"
  let formatted ← Formatter.formatSourceWithEnv env source "imports.lean"
  assertEq "imports stay on separate lines" source formatted

def assertLongImportStaysOnOneLine (env : Lean.Environment) : IO Unit := do
  let source :=
    "import GraphQL.Algorithms.ExecutionUngrouped.Equivalence.AppendSelection.SingleFieldGroup\n"
  let formatted ← Formatter.formatSourceWithEnv env source "long-import.lean"
  assertEq "long import stays on one line" source formatted

def assertNamespaceCommandsStayOnSeparateLines (env : Lean.Environment) : IO Unit := do
  let source :=
    "namespace Outer\n" ++ "namespace Inner\n" ++ "\n" ++ "end Inner\n" ++ "end Outer\n"
  let formatted ← Formatter.formatSourceWithEnv env source "namespace-lines.lean"
  assertEq "namespace commands stay on separate lines" source formatted

def assertCommentsDoNotBlockFormatting (env : Lean.Environment) : IO Unit := do
  let source :=
    "/-! Module comment -/\n"
    ++ "def  first : Nat := 0\n"
    ++ "-- keep line comment\n"
    ++ "def commentedDeclarationBody : Nat := -- keep body comment\n"
    ++ "      veryLongIdentifierNameThatPushesTheDefinitionBodyPastTheWidthLimit\n"
  let expected :=
    "/-! Module comment -/\n"
    ++ "def first : Nat := 0\n"
    ++ "-- keep line comment\n"
    ++ "def commentedDeclarationBody : Nat := -- keep body comment\n"
    ++ "  veryLongIdentifierNameThatPushesTheDefinitionBodyPastTheWidthLimit\n"
  let formatted ← Formatter.formatSourceWithEnv env source "comments-formatting.lean"
  assertEq "comments do not block formatting" expected formatted
  let syntaxCommentSource :=
    "/-! Ground-typed normalization smoke tests use `*InputQuery` and `*OutputSnapshot` pairs. -/\n"
    ++ "/-- Declaration documentation keeps  its exact internal whitespace and line shape. -/\n"
    ++ "def documented : Nat := 0\n"
  let syntaxCommentFormatted ←
    Formatter.formatSourceWithEnv env syntaxCommentSource "syntax-comments.lean"
  assertEq "syntax comments preserve exact source text"
    syntaxCommentSource syntaxCommentFormatted

def assertLeadingCommentsPreserved (env : Lean.Environment) : IO Unit := do
  let source := "-- module comment\n" ++ "\n" ++
    "/- outer /- inner -/ end -/\n" ++ "def commented : Nat := 0\n"
  let formatted ← Formatter.formatSourceWithEnv env source "leading-comments.lean"
  assertEq "leading comments are preserved" source formatted

def assertTrailingLineCommentPreserved (env : Lean.Environment) : IO Unit := do
  let source := "def answer : Nat := 0 -- trailing comment\n"
  let formatted ← Formatter.formatSourceWithEnv env source "trailing-line-comment.lean"
  assertEq "trailing line comment preserved" source formatted

def assertAnonymousConstructorAfterListKeepsSpace (env : Lean.Environment)
    : IO Unit := do
  let source :=
    "def listThenConstructor : Prop := selectionSetTypeConditionFeasible schema objectType [objectType] .allFields selectionSet\n"
  let formatted ←
    Formatter.formatSourceWithEnv env source "list-anonymous-constructor-space.lean"
  assertTextContains "anonymous constructor after list keeps space"
    formatted "[objectType] .allFields"

def assertAttributeDeclarationPreservesSourceBreak (env : Lean.Environment)
    : IO Unit := do
  let source := "@[simp]\n" ++ "def idNat (x : Nat) : Nat := x\n"
  let formatted ← Formatter.formatSourceWithEnv env source "attribute-declaration.lean"
  assertEq "attribute declaration preserves source break" source formatted

def assertAttributesFlowBeforeDeclarations (env : Lean.Environment) : IO Unit := do
  let source :=
    "@[simp] theorem eraseP_nil : [].eraseP p = [] := rfl\n"
    ++ "@[inline] def idNat (x : Nat) : Nat := x\n"
    ++ "@[ext] structure Point where\n"
    ++ "  x : Nat\n"
    ++ "@[derive Repr] inductive Choice where\n"
    ++ "  | left\n"
    ++ "  | right\n"
  let expected :=
    "@[simp] theorem eraseP_nil : [].eraseP p = [] := rfl\n"
    ++ "@[inline] def idNat (x : Nat) : Nat := x\n"
    ++ "@[ext]\n"
    ++ "structure Point where\n"
    ++ "  x : Nat\n"
    ++ "@[derive Repr]\n"
    ++ "inductive Choice where\n"
    ++ "  | left\n"
    ++ "  | right\n"
  let formatted ←
    Formatter.formatSourceWithEnv env source "fitting-attribute-declarations.lean"
  assertEq "attributes stay inline only with single-line declarations" expected
    formatted

  let longSource :=
    "@[simp] theorem theoremNameWithEnoughCharactersToRequireAnAttributeHeaderBreak (value : VeryLongInputTypeName) : VeryLongOutputTypeName := proof\n"
  let longExpected :=
    "@[simp]\n"
    ++ "theorem theoremNameWithEnoughCharactersToRequireAnAttributeHeaderBreak\n"
    ++ "    (value : VeryLongInputTypeName)\n"
    ++ "    : VeryLongOutputTypeName := proof\n"
  let longFormatted ←
    Formatter.formatSourceWithEnv env longSource "long-attribute-declaration.lean"
  assertEq "long attribute breaks before declaration" longExpected longFormatted

  let documentedStructureSource :=
    "/-- Point documentation. -/\n"
    ++ "@[ext] structure DocumentedPoint where\n" ++ "  x : Nat\n"
  let documentedStructureExpected :=
    "/-- Point documentation. -/\n"
    ++ "@[ext]\nstructure DocumentedPoint where\n" ++ "  x : Nat\n"
  let documentedStructureFormatted ←
    Formatter.formatSourceWithEnv env documentedStructureSource
      "documented-attribute-structure.lean"
  assertEq "documentation and attribute flow before a multiline structure"
    documentedStructureExpected documentedStructureFormatted

def assertPrivateTheoremModifierStaysOnHeader (env : Lean.Environment) : IO Unit := do
  let source := "private theorem privateTheoremModifier : True := by\n" ++ "  trivial\n"
  let formatted ←
    Formatter.formatSourceWithEnv env source "private-theorem-modifier.lean"
  assertEq "private theorem modifier stays on header" source formatted

def assertDoBlockPreservesBodyBreak (env : Lean.Environment) : IO Unit := do
  let source :=
    "def lookupObject (schema : Schema) (typeName : Name) : Option ObjectType := do\n"
    ++ "  body\n"
  let formatted ← Formatter.formatSourceWithEnv env source "do-block-body-break.lean"
  assertEq "do block body break" source formatted

def assertDoMatchAlternativesAlignWithMatch (env : Lean.Environment) : IO Unit := do
  let source :=
    "def lookupObject (schema : Schema) (typeName : Name) : Option ObjectType := do\n"
    ++ "  match schema.lookupType typeName with\n"
    ++ "  | some (.object object) => some object\n"
    ++ "  | _ => none\n"
  let formatted ← Formatter.formatSourceWithEnv env source "do-match-alternatives.lean"
  assertEq "do match alternatives align with match" source formatted

def assertDoBlockPreservesStatementBreaks (env : Lean.Environment) : IO Unit := do
  let source :=
    "def lookupField (schema : Schema) (parentType fieldName : Name) : Option FieldDefinition := do\n"
    ++ "  let typeDefinition <- schema.lookupType parentType\n"
    ++ "  let fields <- typeDefinition.fields?\n"
    ++ "  fields.find? (fun field => field.name == fieldName)\n"
  let expected :=
    "def lookupField (schema : Schema) (parentType fieldName : Name)\n"
    ++ "    : Option FieldDefinition := do\n"
    ++ "  let typeDefinition <- schema.lookupType parentType\n"
    ++ "  let fields <- typeDefinition.fields?\n"
    ++ "  fields.find? (fun field => field.name == fieldName)\n"
  let formatted ←
    Formatter.formatSourceWithEnv env source "do-block-statement-breaks.lean"
  assertEq "do block preserves statement breaks" expected formatted

def assertBracketedDoBlockPreservesStatementBreaks (env : Lean.Environment)
    : IO Unit := do
  let source :=
    "def bracketedDo : IO Nat := do {\n"
    ++ "    let n ← pure 1\n"
    ++ "    let m ← pure 2\n"
    ++ "    pure (n + m) }\n"
  let formatted ←
    Formatter.formatSourceWithEnv env source "bracketed-do-statement-breaks.lean"
  assertTrue "bracketed do block preserves code"
    (← codePreservedIgnoringWhitespace env source formatted)
  assertTextContains "bracketed do keeps first statement boundary" formatted
    "let n ← pure 1\n"
  assertTextContains "bracketed do keeps second statement boundary" formatted
    "let m ← pure 2\n"
  assertTextLacks "bracketed do does not flatten adjacent lets" formatted "pure 1 let"

def assertDoLetElseBreaks (env : Lean.Environment) : IO Unit := do
  let header :=
    "def doLetElseExample (atomicTree commaTree : SyntaxTree.Tree)\n"
    ++ "    : Option SyntaxTree.Span := do\n"
  let continuation := "\n" ++ "  some comma.span\n"
  let assertCase (label body expectedBody : String) := do
    let source := header ++ body ++ continuation
    let formatted ←
      try
        Formatter.formatSourceWithEnv env source "do-let-else-breaks.lean"
      catch error =>
        throw <| IO.userError s!"{label}: {error}\n{source}"
    assertEq label (header ++ expectedBody ++ continuation) formatted
  assertCase "do-let fallback breaks multiline value"
    ("  let .leaf comma :=\n"
      ++ "    veryLongAtomicValueNameForDoLetElseFormattingThatCannotShareTheHeaderLine\n"
      ++ "  | none")
    ("  let .leaf comma :=\n"
      ++ "    veryLongAtomicValueNameForDoLetElseFormattingThatCannotShareTheHeaderLine\n"
      ++ "  | none")
  assertCase "do-let fallback breaks multiline alternative"
    ("  let .leaf comma := commaTree | "
      ++ "veryLongAtomicFallbackNameForDoLetElseFormattingThatCannotShareTheHeaderLine")
    ("  let .leaf comma := commaTree\n"
      ++ "  | veryLongAtomicFallbackNameForDoLetElseFormattingThatCannotShareTheHeaderLine")
  assertCase "do-let fallback breaks multiline value and alternative"
    ("  let .leaf comma :=\n"
      ++ "    veryLongAtomicValueNameForDoLetElseFormattingThatCannotShareTheHeaderLine\n"
      ++ "  | veryLongAtomicFallbackNameForDoLetElseFormattingThatCannotShareTheHeaderLine")
    ("  let .leaf comma :=\n"
      ++ "    veryLongAtomicValueNameForDoLetElseFormattingThatCannotShareTheHeaderLine\n"
      ++ "  | veryLongAtomicFallbackNameForDoLetElseFormattingThatCannotShareTheHeaderLine")

def assertDoLetArrowFallbackBreaksBeforeContinuation (env : Lean.Environment)
    : IO Unit := do
  let source :=
    "def veryLongOptionProviderNameForDoLetArrowFallbackBreak\n"
    ++ "    (first second third fourth : Option Nat) : Option (Option Nat) :=\n"
    ++ "  first\n"
    ++ "\n"
    ++ "def fallbackValue : Option Nat := none\n"
    ++ "def assertInstancesCommute : Option Unit := some ()\n"
    ++ "\n"
    ++ "def doLetArrowFallbackExample : Option Nat := do\n"
    ++ "  let .some value ← veryLongOptionProviderNameForDoLetArrowFallbackBreak (some 1) (some 2) (some 3) (some 4) | fallbackValue\n"
    ++ "  assertInstancesCommute\n"
    ++ "  some value\n"
  let expected :=
    "def veryLongOptionProviderNameForDoLetArrowFallbackBreak\n"
    ++ "    (first second third fourth : Option Nat)\n"
    ++ "    : Option (Option Nat) :=\n"
    ++ "  first\n"
    ++ "\n"
    ++ "def fallbackValue : Option Nat := none\n"
    ++ "def assertInstancesCommute : Option Unit := some ()\n"
    ++ "\n"
    ++ "def doLetArrowFallbackExample : Option Nat := do\n"
    ++ "  let .some value ←\n"
    ++ "    veryLongOptionProviderNameForDoLetArrowFallbackBreak (some 1) (some 2) (some 3)\n"
    ++ "      (some 4)\n"
    ++ "  | fallbackValue\n"
    ++ "  assertInstancesCommute\n"
    ++ "  some value\n"
  let formatted ← Formatter.formatSourceWithEnv env source "do-let-arrow-fallback.lean"
  assertEq "do-let arrow fallback breaks before continuation" expected formatted

def assertDoLetExprFallbackBreaksBeforeContinuation (env : Lean.Environment)
    : IO Unit := do
  let source :=
    "import Lean\n\n"
    ++ "open Lean Meta Elab Term\n\n"
    ++ "meta def shortLetExpr : TermElab\n"
    ++ "  | _ => fun _ => do\n"
    ++ "    let_expr A := x | y\n"
    ++ "    z\n"
  let formatted ← Formatter.formatSourceWithEnv env source "do-let-expr-fallback.lean"
  assertTrue "do let_expr fallback preserves code"
    (← codePreservedIgnoringWhitespace env source formatted)
  assertTextContains "do let_expr fallback stays separate from continuation"
    formatted "\n          | y\n          z\n"
  assertTextLacks "do let_expr fallback does not absorb continuation" formatted "| y z"
  let formattedAgain ←
    Formatter.formatSourceWithEnv env formatted "do-let-expr-fallback-formatted.lean"
  assertEq "do let_expr fallback formatting is idempotent" formatted formattedAgain

def assertDoMatchExprAlternativesPreserveBranches (env : Lean.Environment)
    : IO Unit := do
  let source :=
    "import Lean\n\n"
    ++ "open Lean Meta\n\n"
    ++ "meta partial def matchExprExample (e : Expr) : MetaM Expr := do\n"
    ++ "  match_expr ← Meta.whnfR e with\n"
    ++ "  | Matrix.vecCons _ n x xs => do\n"
    ++ "    let tail ← matchExprExample xs\n"
    ++ "    return tail\n"
    ++ "  | _ =>\n"
    ++ "    return e\n"
  let formatted ←
    Formatter.formatSourceWithEnv env source "do-match-expr-alternatives.lean"
  assertTrue "do match_expr alternatives preserve code"
    (← codePreservedIgnoringWhitespace env source formatted)
  assertTextContains "do match_expr branch body starts after arrow" formatted
    "  | Matrix.vecCons _ n x xs =>\n    do\n      let tail ← matchExprExample xs\n"
  assertTextContains "do match_expr fallback branch stays separate"
    formatted "  | _ =>\n    return e\n"
  assertTextLacks "do match_expr alternatives do not merge" formatted "return tail | _"
  let formattedAgain ←
    Formatter.formatSourceWithEnv env formatted
      "do-match-expr-alternatives-formatted.lean"
  assertEq "do match_expr formatting is idempotent" formatted formattedAgain

def assertCommentedMatchExprAlternativesStayParseable (env : Lean.Environment)
    : IO Unit := do
  let source :=
    "import Lean\n\n"
    ++ "open Lean Elab Term Meta\n\n"
    ++ "meta def knownToBeFinsetNotSet (expectedType? : Option Expr) : TermElabM Bool :=\n"
    ++ "  match expectedType? with\n"
    ++ "  | some expectedType =>\n"
    ++ "    match_expr expectedType with\n"
    ++ "    -- If the expected type is known to be `Finset ?α`, return `true`.\n"
    ++ "    | Finset _ => pure true\n"
    ++ "    -- If the expected type is known to be `Set ?α`, give up.\n"
    ++ "    | Set _ => throwUnsupportedSyntax\n"
    ++ "    -- Otherwise return `false`.\n"
    ++ "    | _ => pure false\n"
    ++ "  | none => pure false\n"
  let formatted ← Formatter.formatSourceWithEnv env source "commented-match-expr.lean"
  assertEq "commented match_expr alternatives keep source layout" source formatted
  let _ ← SyntaxTree.parseModuleStringWithEnv env formatted "commented-match-expr.lean"

def assertShowFromBreaksLikeAssignment (env : Lean.Environment) : IO Unit := do
  let source :=
    "def showDoExample : IO Unit :=\n"
    ++ "  show IO Unit\n"
    ++ "    from\n"
    ++ "      do\n"
    ++ "        pure ()\n"
    ++ "\n"
    ++ "def showLongExample : Result :=\n"
    ++ "  show Result from veryLongFunctionNameForShowFormatting firstArgumentNameForShowFormatting secondArgumentNameForShowFormatting thirdArgumentNameForShowFormatting\n"
  let expected :=
    "def showDoExample : IO Unit :=\n"
    ++ "  show IO Unit from do\n"
    ++ "    pure ()\n"
    ++ "\n"
    ++ "def showLongExample : Result :=\n"
    ++ "  show Result from\n"
    ++ "    veryLongFunctionNameForShowFormatting firstArgumentNameForShowFormatting\n"
    ++ "      secondArgumentNameForShowFormatting thirdArgumentNameForShowFormatting\n"
  let formatted ← Formatter.formatSourceWithEnv env source "show-from-breaks.lean"
  assertEq "show/from breaks like assignment" expected formatted

def assertDoControlWrapperRules (env : Lean.Environment) : IO Unit := do
  let source :=
    "def doExamples : IO Unit := do\n"
    ++ "  unless aVeryLongConditionNameForUnlessFormatting && anotherLongConditionName do IO.println \"no\"\n"
    ++ "  state := veryLongFunctionNameForReassignment firstArgumentNameForReassignment secondArgumentNameForReassignment thirdArgumentNameForReassignment\n"
    ++ "  return veryLongFunctionNameForReturn firstArgumentNameForReturn secondArgumentNameForReturn thirdArgumentNameForReturn\n"
    ++ "\n"
    ++ "def forExample : IO Unit := do\n"
    ++ "  for veryLongBinderNameForFormatting in veryLongCollectionFunctionNameForFormatting firstCollectionArgument secondCollectionArgument thirdCollectionArgument do\n"
    ++ "    pure ()\n"
    ++ "\n"
    ++ "def forInfixExample : IO Unit := do\n"
    ++ "  for firstExtremelyLongBinderNameForInfixDepth + secondExtremelyLongBinderNameForInfixDepth + thirdExtremelyLongBinderNameForInfixDepth in shortCollection do\n"
    ++ "    pure ()\n"
  let expected :=
    "def doExamples : IO Unit := do\n"
    ++ "  unless aVeryLongConditionNameForUnlessFormatting && anotherLongConditionName do\n"
    ++ "    IO.println \"no\"\n"
    ++ "  state :=\n"
    ++ "    veryLongFunctionNameForReassignment firstArgumentNameForReassignment\n"
    ++ "      secondArgumentNameForReassignment thirdArgumentNameForReassignment\n"
    ++ "  return veryLongFunctionNameForReturn firstArgumentNameForReturn\n"
    ++ "          secondArgumentNameForReturn thirdArgumentNameForReturn\n"
    ++ "\n"
    ++ "def forExample : IO Unit := do\n"
    ++ "  for veryLongBinderNameForFormatting\n"
    ++ "      in veryLongCollectionFunctionNameForFormatting firstCollectionArgument\n"
    ++ "          secondCollectionArgument thirdCollectionArgument do\n"
    ++ "    pure ()\n"
    ++ "\n"
    ++ "def forInfixExample : IO Unit := do\n"
    ++ "  for firstExtremelyLongBinderNameForInfixDepth\n"
    ++ "        + secondExtremelyLongBinderNameForInfixDepth\n"
    ++ "        + thirdExtremelyLongBinderNameForInfixDepth\n"
    ++ "      in shortCollection do\n"
    ++ "    pure ()\n"
  let formatted ←
    Formatter.formatSourceWithEnv env source "do-control-wrapper-rules.lean"
  assertEq "do control wrapper rules" expected formatted

def assertReturnDoesNotBreakBeforeValue (env : Lean.Environment) : IO Unit := do
  let source :=
    "def returnAnonymousConstructor : Result := do\n"
    ++ "  return ⟨veryLongFunctionNameForReturnConstructor firstArgument secondArgument, anotherVeryLongFunctionNameForReturnConstructor thirdArgument fourthArgument⟩\n"
  let formatted ←
    Formatter.formatSourceWithEnv env source "return-constructor-break.lean"
  assertTextLacks "return keeps value on same line" formatted "return\n"
  let _ ←
    SyntaxTree.parseModuleStringWithEnv env formatted "return-constructor-break.lean"

def assertShowAndDoWrapperRules (env : Lean.Environment) : IO Unit := do
  assertShowFromBreaksLikeAssignment env
  assertDoControlWrapperRules env
  assertReturnDoesNotBreakBeforeValue env
  assertDoLetElseBreaks env
  assertDoLetArrowFallbackBreaksBeforeContinuation env
  assertDoLetExprFallbackBreaksBeforeContinuation env
  assertDoMatchExprAlternativesPreserveBranches env
  assertCommentedMatchExprAlternativesStayParseable env
  assertBracketedDoBlockPreservesStatementBreaks env

def assertProjectionChainDoesNotBreakBeforeDot (env : Lean.Environment) : IO Unit := do
  let source :=
    "def objectTypesImplementingInterface (schema : Schema) (interfaceName : Name) : List Name :=\n"
    ++ "  (schema.objectTypes.filter\n"
    ++ "    (fun objectType =>\n"
    ++ "      schema.objectTypeImplementsInterfaceBool objectType interfaceName)).map ObjectType.name\n"
  let expected :=
    "def objectTypesImplementingInterface (schema : Schema) (interfaceName : Name)\n"
    ++ "    : List Name :=\n"
    ++ "  (schema.objectTypes.filter\n"
    ++ "    (fun objectType =>\n"
    ++ "      schema.objectTypeImplementsInterfaceBool objectType interfaceName)).map\n"
    ++ "    ObjectType.name\n"
  let formatted ←
    Formatter.formatSourceWithEnv env source "projection-chain-dot-break.lean"
  assertEq "projection chain does not break before dot" expected formatted

def assertPipeProjectionKeepsTightDot (env : Lean.Environment) : IO Unit := do
  let source :=
    "theorem pipeProjectionKeepsTightDot\n"
    ++ "    : (values.map (fun value => value.name)) |>.Nodup := by\n"
    ++ "  exact proof\n"
  let formatted ←
    Formatter.formatSourceWithEnv env source "pipe-projection-tight-dot.lean"
  assertEq "pipe projection keeps tight dot" source formatted

def assertLongPipeProjectionKeepsTightDot (env : Lean.Environment) : IO Unit := do
  let source :=
    "theorem collectedExecutableFields_responseNames_nodup_of_singletons\n"
    ++ "    (groups : List (Name × List ExecutableField))\n"
    ++ "    (hsingletons : ∀ responseName fields, (responseName, fields) ∈ groups -> fields.length = 1) :\n"
    ++ "    (collectedExecutableFields groups).map (fun field => field.responseName) |>.Nodup := by\n"
    ++ "  exact proof\n"
  let formatted ←
    Formatter.formatSourceWithEnv env source "long-pipe-projection-tight-dot.lean"
  assertTrue "long pipe projection keeps tight dot" (textContains formatted "|>.Nodup")
  let _ ←
    SyntaxTree.parseModuleStringWithEnv env formatted
      "long-pipe-projection-tight-dot.lean"

def assertPipeProjectionInDeclarationTypeIndentsContinuation (env : Lean.Environment)
    : IO Unit := do
  let source :=
    "theorem collectedExecutableFields_responseNames_nodup_of_singletons\n"
    ++ "    (groups : List (Name × List ExecutableField))\n"
    ++ "    (hsingletons\n"
    ++ "      : ∀ responseName fields, (responseName, fields) ∈ groups -> fields.length = 1)\n"
    ++ "    : (collectedExecutableFields groups).map (fun field => field.responseName) |>.Nodup := by\n"
    ++ "  exact proof\n"
  let expected :=
    "theorem collectedExecutableFields_responseNames_nodup_of_singletons\n"
    ++ "    (groups : List (Name × List ExecutableField))\n"
    ++ "    (hsingletons\n"
    ++ "      : ∀ responseName fields, (responseName, fields) ∈ groups -> fields.length = 1)\n"
    ++ "    : (collectedExecutableFields groups).map (fun field => field.responseName)\n"
    ++ "      |>.Nodup := by\n"
    ++ "  exact proof\n"
  let formatted ←
    Formatter.formatSourceWithEnv env source "pipe-projection-type-continuation.lean"
  assertEq "pipe projection in declaration type indents continuation" expected formatted

def assertPipeProjectionDoesNotBreakAfterDot (env : Lean.Environment) : IO Unit := do
  let source :=
    "def pipeProjectionChain : Result :=\n"
    ++ "  veryLongFunctionNameForPipeProjectionFormatting firstArgument secondArgument thirdArgument |>.trans (anotherVeryLongFunctionNameForPipeProjectionFormatting fourthArgument fifthArgument) |>.symm\n"
  let formatted ←
    Formatter.formatSourceWithEnv env source "pipe-projection-chain-dot.lean"
  assertTextContains "pipe projection chain keeps dot member attached"
    formatted "|>.symm"
  assertTextLacks "pipe projection chain does not break after dot" formatted "|>.\n"
  let _ ←
    SyntaxTree.parseModuleStringWithEnv env formatted "pipe-projection-chain-dot.lean"

def assertMatchAltProofRhsKeepsByOnArrowLine (env : Lean.Environment) : IO Unit := do
  let source :=
    "theorem theoremEquationsAfterMatchReturn : x = y\n"
    ++ "  | [] => by\n"
    ++ "      simp\n"
    ++ "  | _ :: rest => by\n"
    ++ "      simp\n"
  let formatted ← Formatter.formatSourceWithEnv env source "match-alt-proof-rhs.lean"
  assertEq "match alt proof RHS keeps by on arrow line" source formatted

def assertRecordBraceSpacing (env : Lean.Environment) : IO Unit := do
  let source := "def recordLiteral := { data := .null, errors := 1 }\n"
  let formatted ← Formatter.formatSourceWithEnv env source "record-brace-spacing.lean"
  assertEq "record brace spacing" source formatted

def assertDerivingStaysOnOwnLine (env : Lean.Environment) : IO Unit := do
  let source :=
    "structure Response where\n"
    ++ "  data : Nat\n"
    ++ "  errors : Nat := 0\n"
    ++ "deriving Repr\n"
  let formatted ← Formatter.formatSourceWithEnv env source "deriving-own-line.lean"
  assertEq "deriving stays on own line" source formatted

def assertStructureBreaksTopLevelFields (env : Lean.Environment) : IO Unit := do
  let source :=
    "structure CustomScalarType where name : Name deriving Repr, DecidableEq\n"
  let expected :=
    "structure CustomScalarType where\n"
    ++ "  name : Name\n"
    ++ "deriving Repr, DecidableEq\n"
  let formatted ←
    Formatter.formatSourceWithEnv env source "structure-top-level-fields.lean"
  assertEq "structure breaks top-level fields" expected formatted

def assertAbbrevSourceBreakAfterAssign (env : Lean.Environment) : IO Unit := do
  let source := "abbrev Result (α : Type) : Type :=\n" ++ "  Except Nat (α × Nat)\n"
  let formatted ← Formatter.formatSourceWithEnv env source "abbrev-source-assign.lean"
  assertEq "abbrev source break after assignment" source formatted

def assertMatchArmKeepsDoOnArrowLine (env : Lean.Environment) : IO Unit := do
  let source :=
    "def inputValueBoolean? : InputValue -> Option Bool\n"
    ++ "  | .variable name => do\n"
    ++ "      let value <- lookupVariableValue? variableValues name\n"
    ++ "      value.staticBoolean?\n"
    ++ "  | value => value.staticBoolean?\n"
  let formatted ← Formatter.formatSourceWithEnv env source "match-arm-do-rhs.lean"
  assertEq "match arm keeps do on arrow line" source formatted

def assertWhereFormattingKeepsSuffix (env : Lean.Environment) : IO Unit := do
  let source :=
    "def outer : Nat :=\n" ++ "  inner\n" ++ "where\n" ++ "  inner : Nat := 0\n"
  let expected :=
    "def outer : Nat :=\n" ++ "  inner\n" ++ "where\n" ++ "  inner : Nat := 0\n"
  let formatted ← Formatter.formatSourceWithEnv env source "where-formatting.lean"
  assertEq "where formatting keeps suffix" expected formatted

def assertProofBodyUntouched (env : Lean.Environment) : IO Unit := do
  let source :=
    "theorem proofBodyUntouched : True := by\n" ++ "  exact\n" ++ "    True.intro\n"
  let formatted ← Formatter.formatSourceWithEnv env source "proof-body-untouched.lean"
  assertEq "proof body untouched" source formatted

def assertShowProofTermUntouched (env : Lean.Environment) : IO Unit := do
  let source := "#check (show True by\n" ++ "  trivial)\n"
  let formatted ← Formatter.formatSourceWithEnv env source "show-proof-term.lean"
  assertTrue "show proof term preserves code"
    (← codePreservedIgnoringWhitespace env source formatted)
  assertTextContains "show proof term keeps tactic body break"
    formatted "show True by\n"
  assertTextLacks "show proof term does not flatten tactic body" formatted "by trivial"

def assertTheoremTermProofBodyUntouched (env : Lean.Environment) : IO Unit := do
  let source :=
    "theorem theoremTermProofBodyUntouched : True :=\n"
    ++ "  let proof := True.intro\n"
    ++ "  proof\n"
  let formatted ←
    Formatter.formatSourceWithEnv env source "theorem-term-proof-body-untouched.lean"
  assertEq "theorem term proof body untouched" source formatted

def assertTheoremEquationProofBodyUntouched (env : Lean.Environment) : IO Unit := do
  let source :=
    "theorem theoremEquationProofBodyUntouched : Nat -> True\n"
    ++ "  | 0 => by\n"
    ++ "      trivial\n"
    ++ "  | _ + 1 => by\n"
    ++ "      trivial\n"
  let formatted ←
    Formatter.formatSourceWithEnv env source
      "theorem-equation-proof-body-untouched.lean"
  assertEq "theorem equation proof body untouched" source formatted

def assertDefinitionContainingProofUntouched (env : Lean.Environment) : IO Unit := do
  let source :=
    "structure ProofRecord where\n"
    ++ "  proof : True\n"
    ++ "\n"
    ++ "def proofRecordBody : ProofRecord where\n"
    ++ "  proof := by\n"
    ++ "    trivial\n"
  let formatted ←
    Formatter.formatSourceWithEnv env
      source "definition-containing-proof-untouched.lean"
  assertEq "definition containing proof untouched" source formatted

def assertInstanceContainingProofUntouched (env : Lean.Environment) : IO Unit := do
  let source :=
    "instance proofContainingInstance : Inhabited Nat :=\n"
    ++ "  ⟨by\n"
    ++ "    exact 0⟩\n"
  let formatted ←
    Formatter.formatSourceWithEnv env source "instance-containing-proof-untouched.lean"
  assertEq "instance containing proof untouched" source formatted

def assertTerminationProofSuffixUntouched (env : Lean.Environment) : IO Unit := do
  let source :=
    "def recursiveDefinition : Nat -> Nat\n"
    ++ "  | 0 => 0\n"
    ++ "  | n + 1 => recursiveDefinition n\n"
    ++ "termination_by n => n\n"
    ++ "decreasing_by\n"
    ++ "  all_goals\n"
    ++ "    simp\n"
  let formatted ←
    Formatter.formatSourceWithEnv env source "termination-proof-suffix-untouched.lean"
  assertEq "termination proof suffix untouched" source formatted

def assertBasicDeclarationBreak (env : Lean.Environment) : IO Unit := do
  let source :=
    "def declarationTreeBodyBreak : Nat := veryLongIdentifierNameThatPushesTheDefinitionBodyPastTheWidthLimit\n"
  let expected :=
    "def declarationTreeBodyBreak : Nat :=\n"
    ++ "  veryLongIdentifierNameThatPushesTheDefinitionBodyPastTheWidthLimit\n"
  let formatted ← Formatter.formatSourceWithEnv env source "declaration-break.lean"
  assertEq "declaration body break" expected formatted

def assertDeclarationValueInfixBreaksAfterAssign (env : Lean.Environment)
    : IO Unit := do
  let source :=
    "def declarationValueInfixBreakWithLongEnoughHeader : Nat := inferInstanceAs <| OfNat Nat 0\n"
  let expected :=
    "def declarationValueInfixBreakWithLongEnoughHeader : Nat :=\n"
    ++ "  inferInstanceAs <| OfNat Nat 0\n"
  let formatted ←
    Formatter.formatSourceWithEnv env source "declaration-value-infix-break.lean"
  assertEq "declaration value infix breaks after assignment" expected formatted

def assertDeclarationValueKeepsAttachedByBody (env : Lean.Environment) : IO Unit := do
  let source :=
    "instance {VeryLongTypeNameForAttachedBody : Type} [VeryLongClassNameForAttachedBody VeryLongTypeNameForAttachedBody] : Inhabited Nat := makeInhabited veryLongArgumentName <| by\n"
    ++ "    exact 0\n"
  let expected :=
    "instance {VeryLongTypeNameForAttachedBody : Type}\n"
    ++ "    [VeryLongClassNameForAttachedBody VeryLongTypeNameForAttachedBody]\n"
    ++ "    : Inhabited Nat :=\n"
    ++ "  makeInhabited veryLongArgumentName <| by\n"
    ++ "    exact 0\n"
  let formatted ←
    Formatter.formatSourceWithEnv env source "declaration-value-attached-by.lean"
  assertEq "declaration value keeps attached by body" expected formatted
  let formattedAgain ←
    Formatter.formatSourceWithEnv env formatted
      "declaration-value-attached-by-formatted.lean"
  assertEq "declaration value attached by is idempotent" formatted formattedAgain

def assertDeclarationValueKeepsAttachedDoBody (env : Lean.Environment) : IO Unit := do
  let source :=
    "def declarationValueAttachedDoWithLongEnoughHeader : IO Nat := runWithLogging veryLongArgumentName <| do\n"
    ++ "    pure 0\n"
  let expected :=
    "def declarationValueAttachedDoWithLongEnoughHeader : IO Nat :=\n"
    ++ "  runWithLogging veryLongArgumentName <| do\n"
    ++ "    pure 0\n"
  let formatted ←
    Formatter.formatSourceWithEnv env source "declaration-value-attached-do.lean"
  assertEq "declaration value keeps attached do body" expected formatted
  let formattedAgain ←
    Formatter.formatSourceWithEnv env formatted
      "declaration-value-attached-do-formatted.lean"
  assertEq "declaration value attached do is idempotent" formatted formattedAgain

def assertProofValuesRemainLayoutIslands (env : Lean.Environment) : IO Unit := do
  let directSource :=
    "theorem directProofValueLayoutIsland : VeryLongLeftOperandForLayoutTesting = VeryLongRightOperandForLayoutTesting := by\n"
    ++ "  exact proof\n"
  let directExpected :=
    "theorem directProofValueLayoutIsland\n"
    ++ "    : VeryLongLeftOperandForLayoutTesting = VeryLongRightOperandForLayoutTesting := by\n"
    ++ "  exact proof\n"
  let directFormatted ←
    Formatter.formatSourceWithEnv env directSource "direct-proof-value-layout.lean"
  assertEq "direct proof value keeps assignment with by" directExpected directFormatted
  let _ ←
    SyntaxTree.parseModuleStringWithEnv env directFormatted
      "direct-proof-value-layout-formatted.lean"
  let directFormattedAgain ←
    Formatter.formatSourceWithEnv env directFormatted
      "direct-proof-value-layout-formatted.lean"
  assertEq "direct proof value layout is idempotent"
    directFormatted directFormattedAgain
  let whereSource :=
    "theorem whereStructInstProofField (h : VeryLongHypothesisNameForLayoutTesting) : VeryLongTargetTypeNameForLayoutTesting where\n"
    ++ "  field := fun s t hsA htA hs ht hEq => by\n"
    ++ "    exact proof\n"
  let whereExpected :=
    "theorem whereStructInstProofField (h : VeryLongHypothesisNameForLayoutTesting)\n"
    ++ "    : VeryLongTargetTypeNameForLayoutTesting where\n"
    ++ "  field := fun s t hsA htA hs ht hEq => by\n"
    ++ "    exact proof\n"
  let whereFormatted ←
    Formatter.formatSourceWithEnv env whereSource "where-struct-inst-proof-value.lean"
  assertEq "where struct instance proof field remains layout island"
    whereExpected whereFormatted
  let _ ←
    SyntaxTree.parseModuleStringWithEnv env whereFormatted
      "where-struct-inst-proof-value-formatted.lean"
  let whereFormattedAgain ←
    Formatter.formatSourceWithEnv env whereFormatted
      "where-struct-inst-proof-value-formatted.lean"
  assertEq "where struct instance proof layout is idempotent"
    whereFormatted whereFormattedAgain
  let termStructSource :=
    "noncomputable instance [DecidableEq K] : ProjectivePlane (ProjectivePoint K (Fin 3 → K)) (ProjectiveLine K (Fin 3 → K)) :=\n"
    ++ "  { mkPoint := by\n"
    ++ "      intro v w _\n"
    ++ "      exact cross v w\n"
    ++ "    mkPoint_ax := fun h ↦ ⟨cross_orthogonal_left h, cross_orthogonal_right h⟩\n"
    ++ "    mkLine := by\n"
    ++ "      intro v w _\n"
    ++ "      exact cross v w }\n"
  let termStructExpected :=
    "noncomputable instance [DecidableEq K]\n"
    ++ "                  : ProjectivePlane (ProjectivePoint K (Fin 3 → K))\n"
    ++ "                      (ProjectiveLine K (Fin 3 → K)) :=\n"
    ++ "  { mkPoint := by\n"
    ++ "      intro v w _\n"
    ++ "      exact cross v w\n"
    ++ "    mkPoint_ax := fun h ↦ ⟨cross_orthogonal_left h, cross_orthogonal_right h⟩\n"
    ++ "    mkLine := by\n"
    ++ "      intro v w _\n"
    ++ "      exact cross v w }\n"
  let termStructResult ←
    Formatter.formatSourceWithEnvDetailed env termStructSource
      "term-struct-inst-proof-value.lean"
  assertTrue "term struct instance proof field does not fall back"
    (!termStructResult.fellBack)
  assertEq "term struct instance proof field remains layout island"
    termStructExpected termStructResult.formatted
  let _ ←
    SyntaxTree.parseModuleStringWithEnv env termStructResult.formatted
      "term-struct-inst-proof-value-formatted.lean"
  let termStructFormattedAgain ←
    Formatter.formatSourceWithEnv env termStructResult.formatted
      "term-struct-inst-proof-value-formatted.lean"
  assertEq "term struct instance proof layout is idempotent"
    termStructResult.formatted termStructFormattedAgain

def assertCalcLayoutIslandAfterNestedInfix (env : Lean.Environment) : IO Unit := do
  let source :=
    "def embeddingCalcAfterNestedInfix : Nat :=\n"
    ++ "  (firstFunction <| c.sizeUpTo i).trans <| secondFunction <|\n"
    ++ "    calc\n"
    ++ "      c.sizeUpTo i + c.blocksFun i = c.sizeUpTo (i + 1) := (c.sizeUpTo_succ i.2).symm\n"
    ++ "      _ ≤ c.sizeUpTo c.length := monotone_sum_take _ i.2\n"
    ++ "      _ = n := c.sizeUpTo_length\n"
  let expected :=
    "def embeddingCalcAfterNestedInfix : Nat :=\n"
    ++ "  (firstFunction <| c.sizeUpTo i).trans\n"
    ++ "  <| secondFunction\n"
    ++ "  <|\n"
    ++ "    calc\n"
    ++ "      c.sizeUpTo i + c.blocksFun i = c.sizeUpTo (i + 1) := (c.sizeUpTo_succ i.2).symm\n"
    ++ "      _ ≤ c.sizeUpTo c.length := monotone_sum_take _ i.2\n"
    ++ "      _ = n := c.sizeUpTo_length\n"
  let result ←
    Formatter.formatSourceWithEnvDetailed env source
      "calc-layout-island-after-nested-infix.lean"
  assertTrue "calc after nested infix does not fall back" (!result.fellBack)
  assertEq "calc after nested infix preserves calc layout" expected result.formatted
  let _ ←
    SyntaxTree.parseModuleStringWithEnv env result.formatted
      "calc-layout-island-after-nested-infix-formatted.lean"
  let formattedAgain ←
    Formatter.formatSourceWithEnv env result.formatted
      "calc-layout-island-after-nested-infix-formatted.lean"
  assertEq "calc after nested infix is idempotent" result.formatted formattedAgain

def assertHaveTermLayoutIsland (env : Lean.Environment) : IO Unit := do
  let source :=
    "theorem haveTermLayoutWithLongHeaderName (h : VeryLongHypothesisNameForLayoutTesting) : VeryLongTargetNameForLayoutTesting :=\n"
    ++ "  have := firstTerm\n"
    ++ "  secondTerm\n"
  let expected :=
    "theorem haveTermLayoutWithLongHeaderName (h : VeryLongHypothesisNameForLayoutTesting)\n"
    ++ "    : VeryLongTargetNameForLayoutTesting :=\n"
    ++ "  have := firstTerm\n"
    ++ "  secondTerm\n"
  let result ←
    Formatter.formatSourceWithEnvDetailed env source "have-term-layout-island.lean"
  assertTrue "have term layout does not fall back" (!result.fellBack)
  assertEq "have term layout remains an island" expected result.formatted
  let _ ←
    SyntaxTree.parseModuleStringWithEnv env result.formatted
      "have-term-layout-island-formatted.lean"
  let formattedAgain ←
    Formatter.formatSourceWithEnv env result.formatted
      "have-term-layout-island-formatted.lean"
  assertEq "have term layout is idempotent" result.formatted formattedAgain

def assertAbsoluteValueDelimitersStayAttached (env : Lean.Environment) : IO Unit := do
  let source :=
    "notation \"|\" x \"|\" => x\n\n"
    ++ "theorem absoluteValueSignatureWraps (h : VeryLongHypothesisNameForLayoutTesting) : |(firstVeryLongExpressionForAbsoluteValueFormatting + secondVeryLongExpressionForAbsoluteValueFormatting : Int)| ≤ bound := by\n"
    ++ "  exact proof\n"
  let result ←
    Formatter.formatSourceWithEnvDetailed env source "absolute-value-delimiters.lean"
  assertTrue "absolute value delimiters do not trigger fallback" (!result.fellBack)
  assertTextLacks "absolute value opening delimiter stays attached after colon"
    result.formatted ": |\n"
  assertTextLacks "absolute value opening delimiter stays attached after relation"
    result.formatted "≤ |\n"
  let _ ←
    SyntaxTree.parseModuleStringWithEnv env result.formatted
      "absolute-value-delimiters-formatted.lean"
  let formattedAgain ←
    Formatter.formatSourceWithEnv env result.formatted
      "absolute-value-delimiters-formatted.lean"
  assertEq "absolute value formatting is idempotent" result.formatted formattedAgain

def assertSignatureParametersUseLeadingSourceBreakAfterFlatFails
    (env : Lean.Environment)
    : IO Unit := do
  let source :=
    "def definitionSourceBreakAfterNameWhenLongEnoughForLayout\n"
    ++ "    (first : FirstParameterType) (second : SecondParameterType) := body\n"
  let expected :=
    "def definitionSourceBreakAfterNameWhenLongEnoughForLayout\n"
    ++ "    (first : FirstParameterType) (second : SecondParameterType) :=\n"
    ++ "  body\n"
  let formatted ← Formatter.formatSourceWithEnv env source "definition-source-name.lean"
  assertEq "signature parameters use leading source break after flat fails"
    expected formatted

def assertDefinitionSourceBreakAfterAssignOverridesFlat (env : Lean.Environment)
    : IO Unit := do
  let source := "def definitionSourceBreakAfterAssign : Nat :=\n" ++ "  value\n"
  let formatted ←
    Formatter.formatSourceWithEnv env source "definition-source-assign.lean"
  assertEq "definition source break after assignment overrides flat" source formatted

def assertSelfFormattingLetAndArrayRegressions (env : Lean.Environment) : IO Unit := do
  let singletonArray := "def singleton := #[ token]\n"
  let singletonArrayExpected := "def singleton := #[token]\n"
  let singletonArrayFormatted ←
    Formatter.formatSourceWithEnv env singletonArray "singleton-array-spacing.lean"
  assertEq "array literal has tight opening delimiter"
    singletonArrayExpected singletonArrayFormatted

  let destructuringLet :=
    "def filterChildren (children : Array Child) :=\n"
    ++ "  let (children, consumedUntil)\n"
    ++ "      := children.foldl\n"
    ++ "          (fun (filtered, consumedUntil) child =>\n"
    ++ "            let (child, consumedUntil)\n"
    ++ "                := removeOverlappingSourceTokensAux source consumedUntil child\n"
    ++ "            (filtered.push child, consumedUntil))\n"
    ++ "          (#[], consumedUntil)\n"
    ++ "  children\n"
  let destructuringLetExpected :=
    "def filterChildren (children : Array Child) :=\n"
    ++ "  let (children, consumedUntil) :=\n"
    ++ "    children.foldl\n"
    ++ "      (fun (filtered, consumedUntil) child =>\n"
    ++ "        let (child, consumedUntil) :=\n"
    ++ "          removeOverlappingSourceTokensAux source consumedUntil child\n"
    ++ "        (filtered.push child, consumedUntil))\n"
    ++ "      (#[], consumedUntil)\n"
    ++ "  children\n"
  let destructuringLetFormatted ←
    Formatter.formatSourceWithEnv env destructuringLet
      "destructuring-let-assignment.lean"
  assertEq "destructuring let breaks after assignment"
    destructuringLetExpected destructuringLetFormatted

  let typedLet :=
    "def run := do\n"
    ++ "  let\n"
    ++ "    coreContext : Core.Context :=\n"
    ++ "      { fileName := inputContext.fileName, fileMap := inputContext.fileMap }\n"
    ++ "  use coreContext\n"
  let typedLetExpected :=
    "def run := do\n"
    ++ "  let coreContext : Core.Context :=\n"
    ++ "    { fileName := inputContext.fileName, fileMap := inputContext.fileMap }\n"
    ++ "  use coreContext\n"
  let typedLetFormatted ←
    Formatter.formatSourceWithEnv env typedLet "typed-let-header.lean"
  assertEq "let keyword stays with declaration header" typedLetExpected
    typedLetFormatted

def assertCliSelfFormattingRegressions (env : Lean.Environment) : IO Unit := do
  let interpolation :=
    "def parse arg := if arg.startsWith \"-\" then .error s! \"unknown option: { arg }\" else .ok\n"
  let interpolationExpected :=
    "def parse arg := if arg.startsWith \"-\" then .error s!\"unknown option: {arg}\" else .ok\n"
  let interpolationFormatted ←
    Formatter.formatSourceWithEnv env interpolation "interpolation-spacing.lean"
  assertEq "interpolation delimiters stay tight" interpolationExpected
    interpolationFormatted

  let monadicLet :=
    "def check options := do\n"
    ++ "  let\n"
    ++ "    idempotent ←\n"
    ++ "      if options.checkIdempotent then pure true else pure false\n"
    ++ "  pure idempotent\n"
  let monadicLetExpected :=
    "def check options := do\n"
    ++ "  let idempotent ←\n"
    ++ "    if options.checkIdempotent then\n"
    ++ "      pure true\n"
    ++ "    else\n"
    ++ "      pure false\n"
    ++ "  pure idempotent\n"
  let monadicLetFormatted ←
    Formatter.formatSourceWithEnv env monadicLet "monadic-let-assignment.lean"
  assertEq "monadic let breaks after assignment" monadicLetExpected monadicLetFormatted

  let elseIfChain :=
    "def outcome options formatted source := do\n"
    ++ "  if failed then pure .failed\n"
    ++ "  else if formatted == source then\n"
    ++ "    pure .unchanged else if options.check then\n"
    ++ "                      IO.eprintln s! \"needs formatting: { path }\"\n"
    ++ "                      pure .changed\n"
    ++ "  else pure .changed\n"
  let elseIfChainExpected :=
    "def outcome options formatted source := do\n"
    ++ "  if failed then\n"
    ++ "    pure .failed\n"
    ++ "  else if formatted == source then\n"
    ++ "    pure .unchanged\n"
    ++ "  else if options.check then\n"
    ++ "    IO.eprintln s!\"needs formatting: {path}\"\n"
    ++ "    pure .changed\n"
    ++ "  else\n"
    ++ "    pure .changed\n"
  let elseIfChainFormatted ←
    Formatter.formatSourceWithEnv env elseIfChain "else-if-chain.lean"
  assertEq "else-if chain breaks as a balanced chain" elseIfChainExpected
    elseIfChainFormatted

  let semicolonSequence :=
    "def runMain := do\n"
    ++ "  match action with\n"
    ++ "  | .help => IO.println usage;\n"
    ++ "      pure 0\n"
  let semicolonSequenceExpected :=
    "def runMain := do\n"
    ++ "  match action with\n"
    ++ "  | .help => IO.println usage; pure 0\n"
  let semicolonSequenceFormatted ←
    Formatter.formatSourceWithEnv env semicolonSequence "semicolon-sequence.lean"
  assertEq "fitting semicolon sequence stays on one line"
    semicolonSequenceExpected semicolonSequenceFormatted

  let sourceBrokenIf :=
    "def parse arg :=\n"
    ++ "  if arg.startsWith \"-\" then .error s!\"unknown option: {arg}\"\n"
    ++ "  else loop options (FilePath.mk arg :: files) rest\n"
  let sourceBrokenIfExpected :=
    "def parse arg :=\n"
    ++ "  if arg.startsWith \"-\" then\n"
    ++ "    .error s!\"unknown option: {arg}\"\n"
    ++ "  else\n"
    ++ "    loop options (FilePath.mk arg :: files) rest\n"
  let sourceBrokenIfFormatted ←
    Formatter.formatSourceWithEnv env sourceBrokenIf "balanced-source-broken-if.lean"
  assertEq "non-flow if source breaks are balanced"
    sourceBrokenIfExpected sourceBrokenIfFormatted

  let armSourceBrokenIf :=
    "def parseArgs :=\n"
    ++ "  let rec loop : List String → ParseResult\n"
    ++ "    | arg :: rest =>\n"
    ++ "        if arg.startsWith \"-\" then\n"
    ++ "          .error s!\"unknown option: {arg}\"\n"
    ++ "        else loop options (FilePath.mk arg :: files) rest\n"
    ++ "  loop args\n"
  let armSourceBrokenIfExpected :=
    "def parseArgs :=\n"
    ++ "  let rec loop : List String → ParseResult\n"
    ++ "    | arg :: rest =>\n"
    ++ "        if arg.startsWith \"-\" then\n"
    ++ "          .error s!\"unknown option: {arg}\"\n"
    ++ "        else\n"
    ++ "          loop options (FilePath.mk arg :: files) rest\n"
    ++ "  loop args\n"
  let armSourceBrokenIfFormatted ←
    Formatter.formatSourceWithEnv env armSourceBrokenIf
      "balanced-source-broken-if-in-arm.lean"
  assertEq "non-flow if source breaks stay balanced in equation arms"
    armSourceBrokenIfExpected armSourceBrokenIfFormatted

  let monadicTupleLet :=
    "def profile source := do\n"
    ++ "  let (normalizedSource, normalizeMs)\n"
    ++ "      ← timeIO <| pure <| SpaceRules.normalizeLineEndings source\n"
    ++ "  pure (normalizedSource, normalizeMs)\n"
  let monadicTupleLetExpected :=
    "def profile source := do\n"
    ++ "  let (normalizedSource, normalizeMs) ←\n"
    ++ "    timeIO <| pure <| SpaceRules.normalizeLineEndings source\n"
    ++ "  pure (normalizedSource, normalizeMs)\n"
  let monadicTupleLetFormatted ←
    Formatter.formatSourceWithEnv env monadicTupleLet
      "monadic-tuple-let-assignment.lean"
  assertEq "monadic tuple let breaks after assignment"
    monadicTupleLetExpected monadicTupleLetFormatted

  let delimiterHeaders :=
    "def ordinary :=\n"
    ++ "  let value\n"
    ++ "      := computationWithEnoughCharactersToRequireBreaking itsArgument\n"
    ++ "  value\n\n"
    ++ "def equation : Input -> Output\n"
    ++ "  | input\n"
    ++ "      => computationWithEnoughCharactersToRequireBreaking input\n\n"
    ++ "def declarationWithEnoughCharactersToRequireBreaking\n"
    ++ "    (input : Input)\n"
    ++ "    := computationWithEnoughCharactersToRequireBreaking input\n"
  let delimiterHeadersExpected :=
    "def ordinary :=\n"
    ++ "  let value := computationWithEnoughCharactersToRequireBreaking itsArgument\n"
    ++ "  value\n\n"
    ++ "def equation : Input -> Output\n"
    ++ "  | input => computationWithEnoughCharactersToRequireBreaking input\n\n"
    ++ "def declarationWithEnoughCharactersToRequireBreaking (input : Input) :=\n"
    ++ "  computationWithEnoughCharactersToRequireBreaking input\n"
  let delimiterHeadersFormatted ←
    Formatter.formatSourceWithEnv env delimiterHeaders "delimiter-headers.lean"
  assertEq "assignment and arm delimiters stay with their headers"
    delimiterHeadersExpected delimiterHeadersFormatted

  let interpolatedAtom :=
    "def report other := throw <| IO.userError\n"
    ++ "  s!\n"
    ++ "    \"expected infix chain to contain three operands and two operators, got {\n"
    ++ "      repr other}\"\n"
  let interpolatedAtomExpected :=
    "def report other :=\n"
    ++ "  throw\n"
    ++ "  <| IO.userError\n"
    ++ "      s!\"expected infix chain to contain three operands and two operators, got {repr other}\"\n"
  let interpolatedAtomFormatted ←
    Formatter.formatSourceWithEnv env interpolatedAtom "interpolated-string-atom.lean"
  assertEq "interpolated string is a single atom"
    interpolatedAtomExpected interpolatedAtomFormatted

def assertSelfFormattingRulePriorities (env : Lean.Environment) : IO Unit := do
  let flatConstructor :=
    "def short := { ancestors := { segment, childIndex } :: context.ancestors }\n"
  let flatConstructorFormatted ←
    Formatter.formatSourceWithEnv env flatConstructor "flat-constructor.lean"
  assertEq "fitting constructor stays flat" flatConstructor flatConstructorFormatted

  let brokenConstructor :=
    "def RuleContext.push (context : RuleContext) (segment : Segment) (childIndex : Nat)\n"
    ++ "    : RuleContext :=\n"
    ++ "  { ancestors := { segment, childIndex }\n"
    ++ "                  :: context.ancestors }\n"
  let brokenConstructorExpected :=
    "def RuleContext.push (context : RuleContext) (segment : Segment) (childIndex : Nat)\n"
    ++ "    : RuleContext :=\n"
    ++ "  { ancestors := { segment, childIndex } :: context.ancestors }\n"
  let brokenConstructorFormatted ←
    Formatter.formatSourceWithEnv env brokenConstructor "broken-constructor.lean"
  assertEq "broken declaration prefers assignment break before constructor internals"
    brokenConstructorExpected brokenConstructorFormatted

  let optionConstructor :=
    "def boundaryBreak? (segment : Segment) (index indentLevels : Nat) : Option BreakPoint :=\n"
    ++ "  if segment.start < index && index < segment.stop then\n"
    ++ "    some\n"
    ++ "      { index, indentLevels }\n"
    ++ "  else\n"
    ++ "    none\n"
  let optionConstructorExpected :=
    "def boundaryBreak? (segment : Segment) (index indentLevels : Nat) : Option BreakPoint :=\n"
    ++ "  if segment.start < index && index < segment.stop then\n"
    ++ "    some { index, indentLevels }\n"
    ++ "  else\n"
    ++ "    none\n"
  let optionConstructorFormatted ←
    Formatter.formatSourceWithEnv env optionConstructor "option-constructor.lean"
  assertEq "application keeps fitting constructor argument on the same line"
    optionConstructorExpected optionConstructorFormatted

  let equationSource :=
    "def ofTree : SyntaxTree.Tree → Segment\n"
    ++ "  | tree@(.node _ children) =>\n"
    ++ "      { parent := tree, start := 0, stop := children.size }\n"
    ++ "  | tree =>\n"
    ++ "      { parent := tree, start := 0, stop := 0 }\n"
  let equationFormatted ←
    Formatter.formatSourceWithEnv env equationSource "equation-source-breaks.lean"
  assertEq "equation source breaks after arrow are preserved" equationSource
    equationFormatted

  let lambdaSource :=
    "def collect (segment : Segment) :=\n"
    ++ "  segment.indexes.filterMap fun index =>\n"
    ++ "                              match segment.child? index with\n"
    ++ "                              | some child => child\n"
    ++ "                              | none => none\n"
  let lambdaExpected :=
    "def collect (segment : Segment) :=\n"
    ++ "  segment.indexes.filterMap\n"
    ++ "    fun index =>\n"
    ++ "      match segment.child? index with\n"
    ++ "      | some child => child\n"
    ++ "      | none => none\n"
  let lambdaFormatted ←
    Formatter.formatSourceWithEnv env lambdaSource "application-lambda-priority.lean"
  assertEq "application breaks before lambda before preserving its body break"
    lambdaExpected lambdaFormatted

  let multiplePatterns :=
    "def contains (tree : SyntaxTree.Tree) : Bool :=\n"
    ++ "  match tree with\n"
    ++ "  | .node (.raw `Lean.Parser.Command.optDeclSig) children | .node\n"
    ++ "                                                              (.raw\n"
    ++ "                                                                `Lean.Parser.Command.declSig)\n"
    ++ "                                                              children => true\n"
    ++ "  | _ => false\n"
  let multiplePatternsExpected :=
    "def contains (tree : SyntaxTree.Tree) : Bool :=\n"
    ++ "  match tree with\n"
    ++ "  | .node (.raw `Lean.Parser.Command.optDeclSig) children\n"
    ++ "  | .node (.raw `Lean.Parser.Command.declSig) children => true\n"
    ++ "  | _ => false\n"
  let multiplePatternsFormatted ←
    Formatter.formatSourceWithEnv env multiplePatterns "multiple-match-patterns.lean"
  assertEq "multiple match patterns break before the inner alternative"
    multiplePatternsExpected multiplePatternsFormatted

  let longAliasPattern :=
    "def operatorLedMatchConjunction (schema : Schema)\n"
    ++ "    (variableDefinitions : List VariableDefinition)\n"
    ++ "    (parentType : Name)\n"
    ++ "    : Selection -> Prop\n"
    ++ "  | fieldSelection@(.field _responseName fieldName _arguments _directives selectionSet)\n"
    ++ "    =>\n"
    ++ "      Validation.selectionValid schema variableDefinitions parentType fieldSelection\n"
  let longAliasPatternExpected :=
    "def operatorLedMatchConjunction (schema : Schema)\n"
    ++ "    (variableDefinitions : List VariableDefinition)\n"
    ++ "    (parentType : Name)\n"
    ++ "    : Selection -> Prop\n"
    ++ "  | fieldSelection@(\n"
    ++ "        .field _responseName fieldName _arguments _directives selectionSet) =>\n"
    ++ "      Validation.selectionValid schema variableDefinitions parentType fieldSelection\n"
  let longAliasPatternFormatted ←
    Formatter.formatSourceWithEnv env longAliasPattern "long-alias-pattern.lean"
  assertEq "long alias pattern breaks inside parentheses before arrow"
    longAliasPatternExpected longAliasPatternFormatted

  let tracedApplication :=
    "def record state :=\n"
    ++ "  { state with\n"
    ++ "    entries := state.entries\n"
    ++ "                ++ [segmentEntry state output defaultWhitespace segment ruleName\n"
    ++ "                    currentColumn currentIndent segmentIndentation pendingIndent?\n"
    ++ "                    tailIndentation?]\n"
    ++ "  }\n"
  let tracedApplicationExpected :=
    "def record state :=\n"
    ++ "  {\n"
    ++ "    state with\n"
    ++ "      entries :=\n"
    ++ "        state.entries\n"
    ++ "        ++ [segmentEntry state output defaultWhitespace segment ruleName\n"
    ++ "              currentColumn currentIndent segmentIndentation pendingIndent?\n"
    ++ "              tailIndentation?]\n"
    ++ "  }\n"
  let tracedApplicationFormatted ←
    Formatter.formatSourceWithEnv env tracedApplication "traced-application-flow.lean"
  assertEq "application flow uses the field value base"
    tracedApplicationExpected tracedApplicationFormatted

  let multilineFunctionArgument :=
    "def trace state segment ruleName :=\n"
    ++ "  state.trace.recordSegment state.output (fun token =>\n"
    ++ "                                                state.defaultWhitespace token)\n"
    ++ "    segment ruleName\n"
  let multilineFunctionArgumentExpected :=
    "def trace state segment ruleName :=\n"
    ++ "  state.trace.recordSegment state.output\n"
    ++ "    (fun token =>\n"
    ++ "      state.defaultWhitespace token)\n"
    ++ "    segment ruleName\n"
  let multilineFunctionArgumentFormatted ←
    Formatter.formatSourceWithEnv env multilineFunctionArgument
      "multiline-function-argument.lean"
  assertEq "application flow breaks before a multiline function argument"
    multilineFunctionArgumentExpected multilineFunctionArgumentFormatted

  let pipeProjectionFunctionArgument :=
    "def sort xs := xs |>.mergeSort fun left right =>\n"
    ++ "                                  left < right\n"
  let pipeProjectionFunctionArgumentExpected :=
    "def sort xs :=\n"
    ++ "  xs\n"
    ++ "  |>.mergeSort\n"
    ++ "      fun left right =>\n"
    ++ "        left < right\n"
  let pipeProjectionFunctionArgumentFormatted ←
    Formatter.formatSourceWithEnv env pipeProjectionFunctionArgument
      "pipe-projection-function-argument.lean"
  assertEq "pipe projection application breaks before a multiline function argument"
    pipeProjectionFunctionArgumentExpected pipeProjectionFunctionArgumentFormatted

  let bangConjunction :=
    "def choose isFlow state segment breakPoints :=\n"
    ++ "  if !isFlow && !(sourceBreaksAllowedByBreakPointsInState state segment breakPoints).isEmpty then\n"
    ++ "    first\n"
    ++ "  else\n"
    ++ "    second\n"
  let bangConjunctionExpected :=
    "def choose isFlow state segment breakPoints :=\n"
    ++ "  if !isFlow\n"
    ++ "      && !(sourceBreaksAllowedByBreakPointsInState state segment\n"
    ++ "            breakPoints).isEmpty then\n"
    ++ "    first\n"
    ++ "  else\n"
    ++ "    second\n"
  let bangConjunctionFormatted ←
    Formatter.formatSourceWithEnv env bangConjunction "bang-conjunction.lean"
  assertEq "prefix bang stays attached while nested projection suffix fits"
    bangConjunctionExpected bangConjunctionFormatted

  let localEquations :=
    "def fits text trailingWidth :=\n"
    ++ "  let rec loop : List String → Bool\n"
    ++ "  | [] => trailingWidth <= maxLineWidth\n"
    ++ "  | [line] => lineFitsWithTrailingWidth line trailingWidth\n"
    ++ "  | line :: rest => lineFits line && loop rest\n"
    ++ "  loop <| normalize text\n"
  let localEquationsExpected :=
    "def fits text trailingWidth :=\n"
    ++ "  let rec loop : List String → Bool\n"
    ++ "    | [] => trailingWidth <= maxLineWidth\n"
    ++ "    | [line] => lineFitsWithTrailingWidth line trailingWidth\n"
    ++ "    | line :: rest => lineFits line && loop rest\n"
    ++ "  loop <| normalize text\n"
  let localEquationsFormatted ←
    Formatter.formatSourceWithEnv env localEquations "local-equation-indentation.lean"
  assertEq "let rec equation arms indent below the declaration"
    localEquationsExpected localEquationsFormatted

  let localEquationReturn :=
    "def appendedLines (currentLine text : String) : AppendedLines :=\n"
    ++ "  let rec loop (lineWidth breakCount overflowCount : Nat) (current : List Char) :\n"
    ++ "      List Char → AppendedLines\n"
    ++ "    | [] => value\n"
    ++ "  loop 0 0 0 [] text.toList\n"
  let localEquationReturnExpected :=
    "def appendedLines (currentLine text : String) : AppendedLines :=\n"
    ++ "  let rec loop (lineWidth breakCount overflowCount : Nat) (current : List Char)\n"
    ++ "      : List Char → AppendedLines\n"
    ++ "    | [] => value\n"
    ++ "  loop 0 0 0 [] text.toList\n"
  let localEquationReturnFormatted ←
    Formatter.formatSourceWithEnv env localEquationReturn "local-equation-return.lean"
  assertEq "let rec return type breaks before its complete type"
    localEquationReturnExpected localEquationReturnFormatted

  let localFunctionSignature :=
    "def localFunctionExample :=\n"
    ++ "  let renderChild\n"
    ++ "      (state : RenderState) (index : Nat) (child : SyntaxTree.Tree) : RenderState :=\n"
    ++ "    nested state segment index child\n"
    ++ "  renderChild\n"
  let localFunctionSignatureExpected :=
    "def localFunctionExample :=\n"
    ++ "  let renderChild (state : RenderState) (index : Nat) (child : SyntaxTree.Tree)\n"
    ++ "      : RenderState :=\n"
    ++ "    nested state segment index child\n"
    ++ "  renderChild\n"
  let localFunctionSignatureFormatted ←
    Formatter.formatSourceWithEnv env localFunctionSignature
      "local-function-signature.lean"
  assertEq "long local function signature breaks before its return type"
    localFunctionSignatureExpected localFunctionSignatureFormatted

  let structureUpdate :=
    "def append state text :=\n"
    ++ "  { state with\n"
    ++ "      output := state.output ++ text\n"
    ++ "      currentLine := currentLineAfterAppend state.currentLine text\n"
    ++ "  }\n"
  let structureUpdateExpected :=
    "def append state text :=\n"
    ++ "  {\n"
    ++ "    state with\n"
    ++ "      output := state.output ++ text\n"
    ++ "      currentLine := currentLineAfterAppend state.currentLine text\n"
    ++ "  }\n"
  let structureUpdateFormatted ←
    Formatter.formatSourceWithEnv env structureUpdate "structure-update-field-base.lean"
  assertEq "structure update fields use one field indentation"
    structureUpdateExpected structureUpdateFormatted

def assertApplicationFlow (env : Lean.Environment) : IO Unit := do
  let source :=
    "def treeApplicationBody : Result := veryLongFunctionNameForTreeFormatting firstArgumentNameForTree secondArgumentNameForTree thirdArgumentNameForTree\n"
  let expected :=
    "def treeApplicationBody : Result :=\n"
    ++ "  veryLongFunctionNameForTreeFormatting firstArgumentNameForTree\n"
    ++ "    secondArgumentNameForTree thirdArgumentNameForTree\n"
  let formatted ← Formatter.formatSourceWithEnv env source "application-flow.lean"
  assertEq "application flow" expected formatted

def assertApplicationFitsBeforeSourceBreaks (env : Lean.Environment) : IO Unit := do
  let source := "def sourceBreakApplication : Result :=\n" ++ "  f a\n" ++ "    b\n"
  let expected := "def sourceBreakApplication : Result :=\n" ++ "  f a b\n"
  let formatted ←
    Formatter.formatSourceWithEnv env source "application-source-breaks.lean"
  assertEq "application fits before source breaks" expected formatted

def assertNestedApplicationHonorsSourceBreaks (env : Lean.Environment) : IO Unit := do
  let source :=
    "def wrappedApplicationUnderEquationArm : Selection -> Result\n"
    ++ "  | some resolved =>\n"
    ++ "      singleFieldResult responseName\n"
    ++ "        (completeValue schema resolvers variableValues fuel' fieldDefinition.outputType\n"
    ++ "           (field :: fields) resolved)\n"
  let expected :=
    "def wrappedApplicationUnderEquationArm : Selection -> Result\n"
    ++ "  | some resolved =>\n"
    ++ "      singleFieldResult responseName\n"
    ++ "        (completeValue schema resolvers variableValues fuel' fieldDefinition.outputType\n"
    ++ "          (field :: fields) resolved)\n"
  let formatted ←
    Formatter.formatSourceWithEnv env source "nested-application-source-breaks.lean"
  assertEq "nested application source breaks" expected formatted

def assertApplicationArgumentUsesHeadAnchorAfterTypeBreak (env : Lean.Environment)
    : IO Unit := do
  let source :=
    "private theorem size_withoutFieldSelectionsWithResponseName_le (schema : Schema) (responseName : Name) : ∀ selectionSet, SelectionSet.size (withoutFieldSelectionsWithResponseName schema responseName selectionSet) ≤ SelectionSet.size selectionSet := by\n"
    ++ "  exact proof\n"
  let expected :=
    "private theorem size_withoutFieldSelectionsWithResponseName_le (schema : Schema)\n"
    ++ "    (responseName : Name)\n"
    ++ "    : ∀ selectionSet,\n"
    ++ "        SelectionSet.size\n"
    ++ "          (withoutFieldSelectionsWithResponseName schema responseName selectionSet)\n"
    ++ "        ≤ SelectionSet.size selectionSet := by\n"
    ++ "  exact proof\n"
  let formatted ←
    Formatter.formatSourceWithEnv env source
      "application-argument-head-anchor-after-type-break.lean"
  assertEq "application argument uses head anchor after type break" expected formatted

def assertLetExpressionKeepsBodyBreak (env : Lean.Environment) : IO Unit := do
  let source :=
    "def letBodyBreak : Result :=\n" ++ "  let value := f a\n" ++ "  value\n"
  let formatted ← Formatter.formatSourceWithEnv env source "let-body-break.lean"
  assertEq "let expression body break" source formatted

def assertLetIExpressionKeepsBodyBreak (env : Lean.Environment) : IO Unit := do
  let source :=
    "def letIBodyBreak : Result :=\n"
    ++ "  letI : DecidableEq α := decEq\n"
    ++ "  letI : Inhabited β := inhabit\n"
    ++ "  body\n"
  let formatted ← Formatter.formatSourceWithEnv env source "letI-body-break.lean"
  assertTrue "letI expression preserves code"
    (← codePreservedIgnoringWhitespace env source formatted)
  assertTextLacks "letI binding does not absorb following letI" formatted "decEq letI"
  assertTextLacks "letI binding does not absorb final body" formatted "inhabit body"

def assertLetExpressionBlocksFlatRendering (env : Lean.Environment) : IO Unit := do
  let source :=
    "def letBodyBlocksFlat : Prop := let first := value\n" ++ "  Result first\n"
  let expected :=
    "def letBodyBlocksFlat : Prop :=\n"
    ++ "  let first := value\n"
    ++ "  Result first\n"
  let formatted ← Formatter.formatSourceWithEnv env source "let-flat-rendering.lean"
  assertEq "let expression blocks flat rendering" expected formatted

def assertParenthesizedLetRhsIndentUnderImplication (env : Lean.Environment)
    : IO Unit := do
  let source :=
    "def implicationParenthesizedLetOperand : Prop :=\n"
    ++ "  schema.lookupField parentType fieldName = some fieldDefinition\n"
    ++ "  -> (let matching :=\n"
    ++ "      fieldSelectionsWithResponseNameInScope schema parentType responseName rest\n"
    ++ "      result matching)\n"
  let expected :=
    "def implicationParenthesizedLetOperand : Prop :=\n"
    ++ "  schema.lookupField parentType fieldName = some fieldDefinition\n"
    ++ "  -> (let matching :=\n"
    ++ "        fieldSelectionsWithResponseNameInScope schema parentType responseName rest\n"
    ++ "      result matching)\n"
  let formatted ←
    Formatter.formatSourceWithEnv env source
      "parenthesized-let-rhs-under-implication.lean"
  assertEq "parenthesized let RHS indents under implication" expected formatted

def assertLetBodyAfterInfixClosesLetLayout (env : Lean.Environment) : IO Unit := do
  let source :=
    "def implicationLetOperand : Prop :=\n"
    ++ "  ResponseMergeReady (.object fields)\n"
    ++ "  -> let next :=\n"
    ++ "      visitSelection schema resolvers variableValues depth parentType source selection\n"
    ++ "        fields\n"
    ++ "  ResponseMergeReady next\n"
  let expected :=
    "def implicationLetOperand : Prop :=\n"
    ++ "  ResponseMergeReady (.object fields)\n"
    ++ "  ->  let next :=\n"
    ++ "        visitSelection schema resolvers variableValues depth parentType source selection\n"
    ++ "          fields\n"
    ++ "      ResponseMergeReady next\n"
  let formatted ←
    Formatter.formatSourceWithEnv env source
      "let-body-after-infix-closes-let-layout.lean"
  assertEq "let body after infix closes let layout" expected formatted

def assertDeclarationTypeBreak (env : Lean.Environment) : IO Unit := do
  let source :=
    "def declarationHeaderBreak (argumentNameForHeader : ArgumentTypeForHeader) : VeryLongReturnTypeWithEnoughCharactersForLayoutTestingAndMoreText := body\n"
  let expected :=
    "def declarationHeaderBreak (argumentNameForHeader : ArgumentTypeForHeader)\n"
    ++ "    : VeryLongReturnTypeWithEnoughCharactersForLayoutTestingAndMoreText :=\n"
    ++ "  body\n"
  let formatted ← Formatter.formatSourceWithEnv env source "declaration-type-break.lean"
  assertEq "declaration type break" expected formatted

def assertImplicitBinderPreservesTightBraces (env : Lean.Environment) : IO Unit := do
  let source := "def implicitBinder {ObjectRef : Type} : Type := ObjectRef\n"
  let formatted ← Formatter.formatSourceWithEnv env source "implicit-binder-tight.lean"
  assertEq "implicit binder tight braces" source formatted

def assertExplicitBinderTypeBreak (env : Lean.Environment) : IO Unit := do
  let source :=
    "def explicitBinderTypeBreak\n"
    ++ "    (hfields : VeryLongTypeNameWithEnoughCharactersForLayoutTestingAndMoreTextAndExtraExtra) := body\n"
  let expected :=
    "def explicitBinderTypeBreak\n"
    ++ "    (hfields\n"
    ++ "      : VeryLongTypeNameWithEnoughCharactersForLayoutTestingAndMoreTextAndExtraExtra) :=\n"
    ++ "  body\n"
  let formatted ←
    Formatter.formatSourceWithEnv env source "explicit-binder-type-break.lean"
  assertEq "explicit binder type break" expected formatted

def assertGroupedBinderIdentifiersFlow (env : Lean.Environment) : IO Unit := do
  let explicitSource :=
    "def groupedExplicitBinder (rootSelectionSet leftInitialSelectionSet "
    ++ "rightInitialSelectionSet leftCurrentSelectionSet rightCurrentSelectionSet "
    ++ ": List Nat) := 0\n"
  let explicitExpected :=
    "def groupedExplicitBinder\n"
    ++ "    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet\n"
    ++ "      leftCurrentSelectionSet rightCurrentSelectionSet\n"
    ++ "      : List Nat) :=\n"
    ++ "  0\n"
  let explicitFormatted ←
    Formatter.formatSourceWithEnv env explicitSource "grouped-explicit-binder.lean"
  assertEq "grouped explicit binder identifiers flow" explicitExpected explicitFormatted
  let implicitSource :=
    "def groupedImplicitBinder {rootSelectionSet leftInitialSelectionSet "
    ++ "rightInitialSelectionSet leftCurrentSelectionSet rightCurrentSelectionSet "
    ++ ": List Nat} := 0\n"
  let implicitExpected :=
    "def groupedImplicitBinder\n"
    ++ "    {rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet\n"
    ++ "      leftCurrentSelectionSet rightCurrentSelectionSet\n"
    ++ "      : List Nat} :=\n"
    ++ "  0\n"
  let implicitFormatted ←
    Formatter.formatSourceWithEnv env implicitSource "grouped-implicit-binder.lean"
  assertEq "grouped implicit binder identifiers flow" implicitExpected implicitFormatted
  let suffixWidthSource :=
    "def groupedImplicitBinderSuffixWidth\n"
    ++ "    {leftParentType rightParentType rightRuntimeType targetParent leftField "
    ++ "rightField : Name} := 0\n"
  let suffixWidthExpected :=
    "def groupedImplicitBinderSuffixWidth\n"
    ++ "    {leftParentType rightParentType rightRuntimeType targetParent leftField rightField\n"
    ++ "      : Name} :=\n"
    ++ "  0\n"
  let suffixWidthFormatted ←
    Formatter.formatSourceWithEnv env suffixWidthSource
      "grouped-implicit-binder-suffix-width.lean"
  assertEq "grouped binder flow leaves type break to parent"
    suffixWidthExpected suffixWidthFormatted
  for (path, formatted)
      in [
        ("grouped-explicit-binder.lean", explicitFormatted),
        ("grouped-implicit-binder.lean", implicitFormatted),
        ("grouped-implicit-binder-suffix-width.lean", suffixWidthFormatted)
      ] do
    let moduleTree ← SyntaxTree.parseModuleStringWithEnv env formatted path
    assertTrue s!"{path} has no overflow"
      (Formatter.Diagnostics.overflowOccurrences moduleTree).isEmpty

def assertSignatureParametersFitBeforeSourceBreaks (env : Lean.Environment)
    : IO Unit := do
  let source :=
    "def longSignatureName {ObjectIdentity\n"
    ++ "    : Type}\n"
    ++ "    {schema : Schema} := body\n"
  let expected :=
    "def longSignatureName {ObjectIdentity : Type} {schema : Schema} := body\n"
  let formatted ←
    Formatter.formatSourceWithEnv env source "signature-parameter-breaks.lean"
  assertEq "signature parameters fit before source breaks" expected formatted

def assertSignatureParametersStayOnHeaderWhenTheyFit (env : Lean.Environment)
    : IO Unit := do
  let source :=
    "def lookupVariableValue? (variableValues : VariableValues) (name : Name) : Option InputValue := body\n"
  let expected :=
    "def lookupVariableValue? (variableValues : VariableValues) (name : Name)\n"
    ++ "    : Option InputValue :=\n"
    ++ "  body\n"
  let formatted ←
    Formatter.formatSourceWithEnv env source "signature-parameters-fit.lean"
  assertEq "signature parameters stay on header when they fit" expected formatted

def assertSignatureParameterSourceBreakFallback (env : Lean.Environment) : IO Unit := do
  let source :=
    "def ExecutedGroupedSelectionSetAlignedState.of_collected_groups_recursiveAlignedAppendState\n"
    ++ "    {ObjectIdentity : Type}\n"
    ++ "    {schema : Schema} := body\n"
  let expected :=
    "def ExecutedGroupedSelectionSetAlignedState.of_collected_groups_recursiveAlignedAppendState\n"
    ++ "    {ObjectIdentity : Type} {schema : Schema} :=\n"
    ++ "  body\n"
  let formatted ←
    Formatter.formatSourceWithEnv env source "signature-parameter-source-fallback.lean"
  assertEq "signature parameter source break fallback" expected formatted

def assertVariableBinderSequenceFlows (env : Lean.Environment) : IO Unit := do
  let source :=
    "variable {α β₁ β₂ : Type} [CommMonoid α] [CommMonoid β₁] [CommMonoid β₂] {A : Set α} {B₁ : Set β₁} {B₂ : Set β₂} {f₁ : α → β₁} {f₂ : α → β₂} {n : Nat}\n"
  let expected :=
    "variable {α β₁ β₂ : Type} [CommMonoid α] [CommMonoid β₁] [CommMonoid β₂] {A : Set α}\n"
    ++ "  {B₁ : Set β₁} {B₂ : Set β₂} {f₁ : α → β₁} {f₂ : α → β₂} {n : Nat}\n"
  let formatted ← Formatter.formatSourceWithEnv env source "variable-binder-flow.lean"
  assertEq "variable binder sequence flows between binders" expected formatted

def assertMutualEquationArmIndent (env : Lean.Environment) : IO Unit := do
  let source :=
    "mutual\n"
    ++ "  def executeCollectedFields (schema : Schema) (resolvers : Resolvers ObjectRef)\n"
    ++ "      (variableValues : VariableValues) (fuel : Nat)\n"
    ++ "      (source : ResolverValue ObjectRef)\n"
    ++ "    : List (Name × List ExecutableField)\n"
    ++ "      -> Result (List (Name × ResponseValue))\n"
    ++ "  | [] => .ok ([], 0)\n"
    ++ "end\n"
  let expected :=
    "mutual\n"
    ++ "  def executeCollectedFields (schema : Schema) (resolvers : Resolvers ObjectRef)\n"
    ++ "      (variableValues : VariableValues) (fuel : Nat)\n"
    ++ "      (source : ResolverValue ObjectRef)\n"
    ++ "      : List (Name × List ExecutableField) -> Result (List (Name × ResponseValue))\n"
    ++ "    | [] => .ok ([], 0)\n"
    ++ "end\n"
  let formatted ←
    Formatter.formatSourceWithEnv env source "mutual-equation-arm-indent.lean"
  assertEq "mutual equation arm indentation" expected formatted

def assertMutualSingleLineParameterReturnIndent (env : Lean.Environment) : IO Unit := do
  let source :=
    "mutual\n"
    ++ "  def collectSelection (schema : Schema) (variableValues : VariableValues)\n"
    ++ "    : Name -> Value -> Selection -> Result\n"
    ++ "  | parentType, _source,\n"
    ++ "    .field responseName fieldName arguments directives selectionSet =>\n"
    ++ "      body\n"
    ++ "end\n"
  let expected :=
    "mutual\n"
    ++ "  def collectSelection (schema : Schema) (variableValues : VariableValues)\n"
    ++ "      : Name -> Value -> Selection -> Result\n"
    ++ "    | parentType,\n"
    ++ "      _source,\n"
    ++ "      .field responseName fieldName arguments directives selectionSet =>\n"
    ++ "        body\n"
    ++ "end\n"
  let formatted ←
    Formatter.formatSourceWithEnv env source
      "mutual-single-line-parameter-return-indent.lean"
  assertEq "mutual single-line parameter return indentation" expected formatted

def assertReturnTypeInfixIndent (env : Lean.Environment) : IO Unit := do
  let source :=
    "def shapeExample (arg1 : VeryLongTypeNameUsedForLayout) (arg2 : AnotherVeryLongTypeNameUsedForLayout) : VeryLongReturnInputTypeWithEnoughCharactersForLayoutTesting -> VeryLongReturnOutputTypeWithEnoughCharactersForLayoutTesting := body\n"
  let expected :=
    "def shapeExample (arg1 : VeryLongTypeNameUsedForLayout)\n"
    ++ "    (arg2 : AnotherVeryLongTypeNameUsedForLayout)\n"
    ++ "    : VeryLongReturnInputTypeWithEnoughCharactersForLayoutTesting\n"
    ++ "      -> VeryLongReturnOutputTypeWithEnoughCharactersForLayoutTesting :=\n"
    ++ "  body\n"
  let formatted ←
    Formatter.formatSourceWithEnv env source "return-type-infix-indent.lean"
  assertEq "return type infix indentation" expected formatted

def assertReturnTypeArrowFlows (env : Lean.Environment) : IO Unit := do
  let source :=
    "def arrowFlowReturnType : VeryLongInputTypeForArrowFlowTesting -> VeryLongMiddleTypeForArrowFlowTestingExtra -> VeryLongOutputTypeForArrowFlowTesting := body\n"
  let expected :=
    "def arrowFlowReturnType\n"
    ++ "    : VeryLongInputTypeForArrowFlowTesting -> VeryLongMiddleTypeForArrowFlowTestingExtra\n"
    ++ "      -> VeryLongOutputTypeForArrowFlowTesting :=\n"
    ++ "  body\n"
  let formatted ← Formatter.formatSourceWithEnv env source "return-type-arrow-flow.lean"
  assertEq "return type arrow flows" expected formatted

def assertLogicalArrowBreaksBalanced (env : Lean.Environment) : IO Unit := do
  let theoremSource :=
    "theorem theoremArrowBalanced : VeryLongInputTypeForArrowFlowTesting -> VeryLongMiddleTypeForArrowFlowTestingExtra -> VeryLongOutputTypeForArrowFlowTesting := by\n"
    ++ "  exact proof\n"
  let theoremExpected :=
    "theorem theoremArrowBalanced\n"
    ++ "    : VeryLongInputTypeForArrowFlowTesting\n"
    ++ "      -> VeryLongMiddleTypeForArrowFlowTestingExtra\n"
    ++ "      -> VeryLongOutputTypeForArrowFlowTesting := by\n"
    ++ "  exact proof\n"
  let theoremFormatted ←
    Formatter.formatSourceWithEnv env theoremSource "theorem-arrow-balanced.lean"
  assertEq "theorem arrow breaks balanced" theoremExpected theoremFormatted
  let propSource :=
    "def propArrowBalanced : Prop := VeryLongInputTypeForArrowFlowTesting -> VeryLongMiddleTypeForArrowFlowTestingExtra -> VeryLongOutputTypeForArrowFlowTesting\n"
  let propExpected :=
    "def propArrowBalanced : Prop :=\n"
    ++ "  VeryLongInputTypeForArrowFlowTesting\n"
    ++ "  -> VeryLongMiddleTypeForArrowFlowTestingExtra\n"
    ++ "  -> VeryLongOutputTypeForArrowFlowTesting\n"
  let propFormatted ←
    Formatter.formatSourceWithEnv env propSource "prop-arrow-balanced.lean"
  assertEq "Prop definition arrow breaks balanced" propExpected propFormatted

def assertChildFitCountsParentSuffix (env : Lean.Environment) : IO Unit := do
  let source :=
    "theorem theoremLeadingArrowQuantifierReturnDone : schemaWellFormed schema -> ∀ typeName, (schema.getPossibleTypes typeName).Nodup := by\n"
    ++ "  intro hschema\n"
    ++ "  exact proof\n"
  let expected :=
    "theorem theoremLeadingArrowQuantifierReturnDone\n"
    ++ "    : schemaWellFormed schema\n"
    ++ "      -> ∀ typeName, (schema.getPossibleTypes typeName).Nodup := by\n"
    ++ "  intro hschema\n"
    ++ "  exact proof\n"
  let formatted ←
    Formatter.formatSourceWithEnv env source "child-fit-parent-suffix.lean"
  assertEq "child fit counts parent suffix" expected formatted

def assertColumnIndentationIsConservative : IO Unit := do
  assertTrue "column 3 needs only one indentation level"
    (Formatter.indentationLevelForColumn 3 == 1)
  assertTrue "column 3 rounds forward to the next indentation level"
    (Formatter.indentationPastColumn 3 == 4)
  assertTrue "ordinary breaks indent from their rounded base"
    (Formatter.breakIndent 3 2 { index := 0, indentLevels := 1 } == 6)

def tokenAt (lexeme : String) (start stop : String.Pos.Raw) : SyntaxTree.Token :=
  {
    role := .ident
    kind := Lean.identKind
    value := lexeme
    lexeme
    leading := SyntaxTree.syntheticTrivia
    trailing := SyntaxTree.syntheticTrivia
    span := { start, stop }
  }

def assertSegmentBaseUsesRenderedStartColumn : IO Unit := do
  let source := "left\n      right"
  let left := tokenAt "left" (String.Pos.Raw.mk 0) (String.Pos.Raw.mk 4)
  let right := tokenAt "right" (String.Pos.Raw.mk 11) (String.Pos.Raw.mk 16)
  let state : Formatter.RenderState :=
    {
      source
      output := "left"
      currentLine := "left"
      lastToken? := some left
      segmentBaseColumn := 2
      segmentIndentation := 1
    }
  let base :=
    state.segmentStartBaseFor (Formatter.LineBreakRules.Segment.ofTree (.leaf right))
  assertTrue "segment base uses rendered start column, not source indentation"
    (base.column == 5 && base.indentation == 2)

def assertListApplicationColumnIndent (env : Lean.Environment) : IO Unit := do
  let source :=
    "def listWrapper := [.inlineFragment none [directiveForBit varName value] (wrapWithBoolCase rest selectionSet)]\n"
  let expected :=
    "def listWrapper :=\n"
    ++ "  [.inlineFragment none [directiveForBit varName value]\n"
    ++ "    (wrapWithBoolCase rest selectionSet)]\n"
  let formatted ←
    Formatter.formatSourceWithEnv env source "list-application-column-indent.lean"
  assertEq "list application column indentation" expected formatted

def assertListApplicationSourceBreakIndent (env : Lean.Environment) : IO Unit := do
  let source :=
    "def listWrapper :=\n"
    ++ "  [.inlineFragment none [directiveForBit varName value]\n"
    ++ "      (wrapWithBoolCase rest selectionSet)]\n"
  let expected :=
    "def listWrapper :=\n"
    ++ "  [.inlineFragment none [directiveForBit varName value]\n"
    ++ "    (wrapWithBoolCase rest selectionSet)]\n"
  let formatted ←
    Formatter.formatSourceWithEnv env source "list-application-source-break-indent.lean"
  assertEq "list application source break indentation" expected formatted

def assertSingletonArrayKeepsBodyBase (env : Lean.Environment) : IO Unit := do
  let source :=
    "def collectFields := [{ parentType := parentType, responseName := responseName, fieldName := fieldName, arguments := arguments, outputType := fieldDefinition.outputType, selectionSet := selectionSet }]\n"
  let expected :=
    "def collectFields :=\n"
    ++ "  [{\n"
    ++ "    parentType := parentType,\n"
    ++ "    responseName := responseName,\n"
    ++ "    fieldName := fieldName,\n"
    ++ "    arguments := arguments,\n"
    ++ "    outputType := fieldDefinition.outputType,\n"
    ++ "    selectionSet := selectionSet\n"
    ++ "  }]\n"
  let formatted ← Formatter.formatSourceWithEnv env source "singleton-array-base.lean"
  assertEq "singleton array keeps body base" expected formatted

def assertMultiItemArrayBreaksBalanced (env : Lean.Environment) : IO Unit := do
  let source :=
    "def builtinScalarDefinitions : List TypeDefinition := [.builtinScalar .int, .builtinScalar .float, .builtinScalar .string, .builtinScalar .boolean, .builtinScalar .id]\n"
  let expected :=
    "def builtinScalarDefinitions : List TypeDefinition :=\n"
    ++ "  [\n"
    ++ "    .builtinScalar .int,\n"
    ++ "    .builtinScalar .float,\n"
    ++ "    .builtinScalar .string,\n"
    ++ "    .builtinScalar .boolean,\n"
    ++ "    .builtinScalar .id\n"
    ++ "  ]\n"
  let formatted ←
    Formatter.formatSourceWithEnv env source "multi-item-array-balanced.lean"
  assertEq "multi-item array breaks balanced" expected formatted

def assertOffColumnArrayRoundsOneLevel (env : Lean.Environment) : IO Unit := do
  let source :=
    "def offColumnArray := some <| #[firstExceptionallyLongItemNameForOffColumnArrayLayout, secondExceptionallyLongItemNameForOffColumnArrayLayout] ++ remainingItemsForOffColumnArrayLayout\n"
  let expected :=
    "def offColumnArray :=\n"
    ++ "  some\n"
    ++ "  <| #[\n"
    ++ "        firstExceptionallyLongItemNameForOffColumnArrayLayout,\n"
    ++ "        secondExceptionallyLongItemNameForOffColumnArrayLayout\n"
    ++ "      ]\n"
    ++ "      ++ remainingItemsForOffColumnArrayLayout\n"
  let formatted ←
    Formatter.formatSourceWithEnv env source "off-column-array-balanced.lean"
  assertEq "off-column array items indent one level past the rounded opener" expected
    formatted

def assertInstanceWhereStaysWithHeader (env : Lean.Environment) : IO Unit := do
  let source :=
    "instance instCoeOptionValueToValue {ObjectRef : Type} :\n"
    ++ "    Coe (Option (ResolverValue ObjectRef)) (ResolverValue ObjectRef) where\n"
    ++ "  coe := resolvedValueOrNull\n"
  let expected :=
    "instance instCoeOptionValueToValue {ObjectRef : Type}\n"
    ++ "    : Coe (Option (ResolverValue ObjectRef)) (ResolverValue ObjectRef) where\n"
    ++ "  coe := resolvedValueOrNull\n"
  let formatted ←
    Formatter.formatSourceWithEnv env source "instance-type-leading-source-break.lean"
  assertEq "instance where stays with header" expected formatted

def assertInfixLeftDepth (env : Lean.Environment) : IO Unit := do
  let source :=
    "def nestedInfix : Prop := Schema.lookupFieldDefinition implementationFields interfaceField.name = some implementationField ∧ fieldDefinitionImplements schema implementationField interfaceField\n"
  let expected :=
    "def nestedInfix : Prop :=\n"
    ++ "  Schema.lookupFieldDefinition implementationFields interfaceField.name\n"
    ++ "    = some implementationField\n"
    ++ "  ∧ fieldDefinitionImplements schema implementationField interfaceField\n"
  let formatted ← Formatter.formatSourceWithEnv env source "infix-left-depth.lean"
  assertEq "infix-left-depth formatting" expected formatted

def assertInfixIgnoresFittingSourceBreaks (env : Lean.Environment) : IO Unit := do
  let source :=
    "def sourceBreakInfix : Prop :=\n"
    ++ "  firstCondition\n"
    ++ "  ∧ secondCondition\n"
  let expected :=
    "def sourceBreakInfix : Prop :=\n" ++ "  firstCondition ∧ secondCondition\n"
  let formatted ← Formatter.formatSourceWithEnv env source "infix-source-breaks.lean"
  assertEq "infix ignores fitting source breaks" expected formatted

def assertInfixIgnoresArbitrarySourceBreaks (env : Lean.Environment) : IO Unit := do
  let source :=
    "def arbitraryInfixSourceBreak : Prop := firstCondition ∧\n"
    ++ "  secondCondition\n"
  let expected :=
    "def arbitraryInfixSourceBreak : Prop := firstCondition ∧ secondCondition\n"
  let formatted ←
    Formatter.formatSourceWithEnv env source "infix-arbitrary-source-breaks.lean"
  assertEq "infix ignores arbitrary source breaks" expected formatted

def assertInfixRhsFitsBeforeSourceBreaks (env : Lean.Environment) : IO Unit := do
  let source :=
    "def selectionDirectiveFree : Selection -> Prop\n"
    ++ "  | .field _responseName _fieldName _arguments directives selectionSet =>\n"
    ++ "      directives\n"
    ++ "        = []\n"
    ++ "      ∧ selectionSetDirectiveFree selectionSet\n"
  let expected :=
    "def selectionDirectiveFree : Selection -> Prop\n"
    ++ "  | .field _responseName _fieldName _arguments directives selectionSet =>\n"
    ++ "      directives = [] ∧ selectionSetDirectiveFree selectionSet\n"
  let formatted ←
    Formatter.formatSourceWithEnv env source "selection-directive-free.lean"
  assertEq "infix RHS fits before source breaks" expected formatted

def assertLogicalArrowSourceBreakIdempotent (env : Lean.Environment) : IO Unit := do
  let source :=
    "def logicalArrowSourceBreak : Prop :=\n"
    ++ "  schema.typesOverlapBool parentType typeCondition = true ->\n"
    ++ "    ∀ objectType, body objectType\n"
  let expected :=
    "def logicalArrowSourceBreak : Prop :=\n"
    ++ "  schema.typesOverlapBool parentType typeCondition = true\n"
    ++ "  -> ∀ objectType, body objectType\n"
  let once ← Formatter.formatSourceWithEnv env source "logical-arrow-source-break.lean"
  assertEq "logical arrow ignores source break before quantifier" expected once
  let twice ← Formatter.formatSourceWithEnv env once "logical-arrow-source-break.lean"
  assertEq "logical arrow source break idempotence" once twice

def assertApplicationSourceBreakInInfixLeftOperand (env : Lean.Environment)
    : IO Unit := do
  let source :=
    "def equalityInWrappedImplicationOperand : Prop :=\n"
    ++ "  operationBoolVarsComplete operation variableValues\n"
    ++ "  -> Execution.executeQueryWithFuel schema resolvers variableValues operation fuel\n"
    ++ "      source\n"
    ++ "      = Execution.executeQueryWithFuel schema resolvers variableValues\n"
    ++ "          (completeNormalizeOperation schema operation) fuel source\n"
  let expected :=
    "def equalityInWrappedImplicationOperand : Prop :=\n"
    ++ "  operationBoolVarsComplete operation variableValues\n"
    ++ "  -> Execution.executeQueryWithFuel schema resolvers variableValues operation fuel\n"
    ++ "        source\n"
    ++ "      = Execution.executeQueryWithFuel schema resolvers variableValues\n"
    ++ "          (completeNormalizeOperation schema operation) fuel source\n"
  let formatted ←
    Formatter.formatSourceWithEnv env source
      "application-source-break-in-infix-left-operand.lean"
  assertEq "application source break in infix left operand" expected formatted

def assertApplicationFlowBreakKeepsInfixDepthIdempotent (env : Lean.Environment)
    : IO Unit := do
  let source :=
    "theorem executeField_object_append_fresh_eq\n"
    ++ "    {ObjectIdentity : Type}\n"
    ++ "    (schema : Schema) (resolvers : Resolvers ObjectIdentity)\n"
    ++ "    (variableValues : VariableValues) (depth : Nat)\n"
    ++ "    (source : ResolverValue ObjectIdentity) (field : ExecutableField)\n"
    ++ "    (prefixFields suffix : List (Name × ResponseValue)) :\n"
    ++ "      field.responseName ∉ prefixFields.map Prod.fst ->\n"
    ++ "        executeField schema resolvers variableValues depth source\n"
    ++ "          (responseObjectField? field.responseName\n"
    ++ "            (.object (prefixFields ++ suffix))) field =\n"
    ++ "        executeField schema resolvers variableValues depth source\n"
    ++ "          (responseObjectField? field.responseName (.object suffix)) field := by\n"
    ++ "  exact proof\n"
  let expected :=
    "theorem executeField_object_append_fresh_eq\n"
    ++ "    {ObjectIdentity : Type}\n"
    ++ "    (schema : Schema) (resolvers : Resolvers ObjectIdentity)\n"
    ++ "    (variableValues : VariableValues) (depth : Nat)\n"
    ++ "    (source : ResolverValue ObjectIdentity) (field : ExecutableField)\n"
    ++ "    (prefixFields suffix : List (Name × ResponseValue))\n"
    ++ "    : field.responseName ∉ prefixFields.map Prod.fst\n"
    ++ "      -> executeField schema resolvers variableValues depth source\n"
    ++ "            (responseObjectField? field.responseName (.object (prefixFields ++ suffix)))\n"
    ++ "            field\n"
    ++ "          = executeField schema resolvers variableValues depth source\n"
    ++ "              (responseObjectField? field.responseName (.object suffix)) field := by\n"
    ++ "  exact proof\n"
  let once ←
    Formatter.formatSourceWithEnv env source
      "application-flow-infix-depth-idempotent.lean"
  assertEq "application flow break keeps infix depth" expected once
  let twice ←
    Formatter.formatSourceWithEnv env once
      "application-flow-infix-depth-idempotent.lean"
  assertEq "application flow break keeps infix depth idempotent" once twice

def assertQuantifierBodyIgnoresParentInfixLeftDepth (env : Lean.Environment)
    : IO Unit := do
  let source :=
    "def conjunctionBeforeParenthesizedQuantifier : Prop :=\n"
    ++ "  (arguments.map Argument.name).Nodup\n"
    ++ "  ∧ (∀ argument,\n"
    ++ "        argument ∈ arguments\n"
    ++ "          -> argumentValid schema definitions variableDefinitions argument)\n"
  let expected :=
    "def conjunctionBeforeParenthesizedQuantifier : Prop :=\n"
    ++ "  (arguments.map Argument.name).Nodup\n"
    ++ "  ∧ (∀ argument,\n"
    ++ "      argument ∈ arguments\n"
    ++ "      -> argumentValid schema definitions variableDefinitions argument)\n"
  let formatted ←
    Formatter.formatSourceWithEnv env source
      "quantifier-body-ignore-parent-infix-depth.lean"
  assertEq "quantifier body ignores parent infix-left depth" expected formatted

def assertParenthesizedQuantifierBlockIgnoresParentInfixLeftDepth
    (env : Lean.Environment)
    : IO Unit := do
  let source :=
    "def parenthesizedConjunctionBlockSequence : Prop :=\n"
    ++ "  variables.Nodup\n"
    ++ "  ∧ (∀ selection,\n"
    ++ "      selection ∈ selectionSet\n"
    ++ "        -> ∃ boolCase body,\n"
    ++ "            completeNormalBoolCase variables boolCase\n"
    ++ "              ∧ completeNormalBooleanStem boolCase selection body\n"
    ++ "              ∧ selectionSetNormal schema body\n"
    ++ "              ∧ selectionSetDirectiveFree body)\n"
    ++ "  ∧ (∀ left right,\n"
    ++ "      left ∈ selectionSet\n"
    ++ "      -> right ∈ selectionSet)\n"
  let expected :=
    "def parenthesizedConjunctionBlockSequence : Prop :=\n"
    ++ "  variables.Nodup\n"
    ++ "  ∧ (∀ selection,\n"
    ++ "      selection ∈ selectionSet\n"
    ++ "      -> ∃ boolCase body,\n"
    ++ "          completeNormalBoolCase variables boolCase\n"
    ++ "          ∧ completeNormalBooleanStem boolCase selection body\n"
    ++ "          ∧ selectionSetNormal schema body\n"
    ++ "          ∧ selectionSetDirectiveFree body)\n"
    ++ "  ∧ (∀ left right, left ∈ selectionSet -> right ∈ selectionSet)\n"
  let formatted ←
    Formatter.formatSourceWithEnv env source
      "parenthesized-quantifier-block-ignore-parent-infix-depth.lean"
  assertEq "parenthesized quantifier block ignores parent infix-left depth"
    expected formatted

def assertNestedInfixDoesNotDoubleCountOperatorWidth (env : Lean.Environment)
    : IO Unit := do
  let source :=
    "def hasUnscopedSetOption (line : String) : Bool :=\n"
    ++ "  let trimmed := trimLeft line\n"
    ++ "  trimmed.startsWith \"set_option\"\n"
    ++ "  && (trimmed.contains \"trace\"\n"
    ++ "        || trimmed.contains \"pp.\"\n"
    ++ "        || trimmed.contains \"profiler\"\n"
    ++ "        || trimmed.contains \"maxHeartbeats\")\n"
    ++ "  && !trimmed.contains \" in \"\n"
  let expected :=
    "def hasUnscopedSetOption (line : String) : Bool :=\n"
    ++ "  let trimmed := trimLeft line\n"
    ++ "  trimmed.startsWith \"set_option\"\n"
    ++ "  && (trimmed.contains \"trace\"\n"
    ++ "      || trimmed.contains \"pp.\"\n"
    ++ "      || trimmed.contains \"profiler\"\n"
    ++ "      || trimmed.contains \"maxHeartbeats\")\n"
    ++ "  && !trimmed.contains \" in \"\n"
  let formatted ←
    Formatter.formatSourceWithEnv env source "nested-infix-operator-width.lean"
  assertEq "nested infix does not double-count operator width" expected formatted

def assertNestedInfixKeepsHierarchy (env : Lean.Environment) : IO Unit := do
  let source :=
    "def nestedAppendLhs :=\n"
    ++ "  ((executableFieldSelectionsWithEnoughCharactersForLayoutTesting [first] ++ middle ++ executableFieldSelectionsWithEnoughCharactersForLayoutTesting [later]) ++ suffix)\n"
    ++ "\n"
    ++ "def nestedConsLhs :=\n"
    ++ "  (({ parentType := parentType, responseName := responseName, fieldName := fieldName, arguments := arguments, selectionSet := selectionSet } :: fields) ++ [{ parentType := parentType, responseName := responseName, fieldName := fieldName, arguments := laterArguments, selectionSet := laterSelectionSet }])\n"
  let expected :=
    "def nestedAppendLhs :=\n"
    ++ "  ((executableFieldSelectionsWithEnoughCharactersForLayoutTesting [first]\n"
    ++ "      ++ middle\n"
    ++ "      ++ executableFieldSelectionsWithEnoughCharactersForLayoutTesting [later])\n"
    ++ "    ++ suffix)\n"
    ++ "\n"
    ++ "def nestedConsLhs :=\n"
    ++ "  (({\n"
    ++ "        parentType := parentType,\n"
    ++ "        responseName := responseName,\n"
    ++ "        fieldName := fieldName,\n"
    ++ "        arguments := arguments,\n"
    ++ "        selectionSet := selectionSet\n"
    ++ "      }\n"
    ++ "      :: fields)\n"
    ++ "    ++ [{\n"
    ++ "          parentType := parentType,\n"
    ++ "          responseName := responseName,\n"
    ++ "          fieldName := fieldName,\n"
    ++ "          arguments := laterArguments,\n"
    ++ "          selectionSet := laterSelectionSet\n"
    ++ "        }])\n"
  let formatted ←
    Formatter.formatSourceWithEnv env source "nested-infix-lhs-hierarchy.lean"
  assertEq "nested infix keeps hierarchy" expected formatted

def assertApplicationInNestedInfixKeepsHierarchy (env : Lean.Environment)
    : IO Unit := do
  let source :=
    "def nestedApplicationConsAppend : Prop :=\n"
    ++ "  premise\n"
    ++ "  -> VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues\n"
    ++ "      depth parentType source\n"
    ++ "      (Selection.field responseName fieldName arguments fieldDirectives\n"
    ++ "          fieldSelectionSet\n"
    ++ "        :: inlineSelectionSet\n"
    ++ "        ++ rest)\n"
  let expected :=
    "def nestedApplicationConsAppend : Prop :=\n"
    ++ "  premise\n"
    ++ "  -> VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues\n"
    ++ "      depth parentType source\n"
    ++ "      (Selection.field responseName fieldName arguments fieldDirectives\n"
    ++ "            fieldSelectionSet\n"
    ++ "          :: inlineSelectionSet\n"
    ++ "        ++ rest)\n"
  let formatted ←
    Formatter.formatSourceWithEnv env source
      "application-in-nested-infix-hierarchy.lean"
  assertEq "application in nested infix keeps hierarchy" expected formatted

def assertNestedLogicalApplicationLhsKeepsHierarchy (env : Lean.Environment)
    : IO Unit := do
  let source :=
    "theorem nestedLogicalApplicationLhs\n"
    ++ "    : schema.lookupField parentType fieldName = some fieldDefinition\n"
    ++ "      -> ((objectTypeNameBool schema fieldDefinition.outputType.namedType = true\n"
    ++ "            ∧ runtimeType = fieldDefinition.outputType.namedType)\n"
    ++ "          ∨ ((TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool schema\n"
    ++ "              = true\n"
    ++ "              ∧ objectTypeNameBool schema fieldDefinition.outputType.namedType = false)) := by\n"
    ++ "  exact proof\n"
  let expected :=
    "theorem nestedLogicalApplicationLhs\n"
    ++ "    : schema.lookupField parentType fieldName = some fieldDefinition\n"
    ++ "      -> ((objectTypeNameBool schema fieldDefinition.outputType.namedType = true\n"
    ++ "            ∧ runtimeType = fieldDefinition.outputType.namedType)\n"
    ++ "          ∨ ((TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool schema\n"
    ++ "                = true\n"
    ++ "              ∧ objectTypeNameBool schema fieldDefinition.outputType.namedType\n"
    ++ "                = false)) := by\n"
    ++ "  exact proof\n"
  let formatted ←
    Formatter.formatSourceWithEnv env source "nested-logical-application-lhs.lean"
  assertEq "nested logical application LHS keeps hierarchy" expected formatted

def assertSubtypeBreaksBeforeProperty (env : Lean.Environment) : IO Unit := do
  let source :=
    "def subtypeBreak : Prop := { targetField : ScopedFieldVeryLongTypeNameLikeThis // targetField ∈ targetFieldsWithVeryLongName }\n"
  let expected :=
    "def subtypeBreak : Prop :=\n"
    ++ "  { targetField : ScopedFieldVeryLongTypeNameLikeThis\n"
    ++ "    // targetField ∈ targetFieldsWithVeryLongName }\n"
  let formatted ← Formatter.formatSourceWithEnv env source "subtype-break.lean"
  assertEq "subtype breaks before property" expected formatted

def assertAdjacentQuantifiersFitBeforeSourceBreaks (env : Lean.Environment)
    : IO Unit := do
  let source :=
    "def adjacentQuantifiers : Prop :=\n"
    ++ "  ∀ x,\n"
    ++ "    ∀ y,\n"
    ++ "      body x y\n"
  let expected := "def adjacentQuantifiers : Prop :=\n" ++ "  ∀ x, ∀ y, body x y\n"
  let formatted ←
    Formatter.formatSourceWithEnv env source "adjacent-quantifiers-source-breaks.lean"
  assertEq "adjacent quantifiers fit before source breaks" expected formatted

def assertIfThenElseRuleBreaksBalancedShape (env : Lean.Environment) : IO Unit := do
  let source :=
    "def ifElseAfterQualifiedArgument : Result :=\n"
    ++ "  if responseName == group.fst then\n"
    ++ "    (responseName, fields ++ group.snd) :: rest\n"
    ++ "  else\n"
    ++ "    (responseName, fields) :: addExecutableGroup group rest\n"
  let formatted ← Formatter.formatSourceWithEnv env source "if-then-else-breaks.lean"
  assertEq "if-then-else rule breaks balanced shape" source formatted

def assertShortIfThenElseStaysFlatInEquationArm (env : Lean.Environment) : IO Unit := do
  let source :=
    "def lookupVariableValue? : VariableValues -> Option InputValue\n"
    ++ "  | [] => none\n"
    ++ "  | (variableName, value) :: rest =>\n"
    ++ "      if variableName = name then some value else lookupVariableValue? rest name\n"
  let expected :=
    "def lookupVariableValue? : VariableValues -> Option InputValue\n"
    ++ "  | [] => none\n"
    ++ "  | (variableName, value) :: rest =>\n"
    ++ "      if variableName = name then some value else lookupVariableValue? rest name\n"
  let formatted ←
    Formatter.formatSourceWithEnv env source "if-then-else-flat-equation-arm.lean"
  assertEq "short if-then-else stays flat in equation arm" expected formatted

def assertIfThenElseUsesExistingBreaks (env : Lean.Environment) : IO Unit := do
  let source :=
    "def sourceBrokenIf : Result :=\n"
    ++ "  if condition then\n"
    ++ "    first\n"
    ++ "  else\n"
    ++ "    second\n"
  let formatted ←
    Formatter.formatSourceWithEnv env source "if-then-else-existing-breaks.lean"
  assertEq "if-then-else uses existing breaks" source formatted

def assertElseIfContinuesOnElseLine (env : Lean.Environment) : IO Unit := do
  let source :=
    "def elseIfChain : Result := if conditionNameWithEnoughCharactersForLayoutTesting then firstResultNameWithEnoughCharactersForLayoutTesting else if secondConditionNameWithEnoughCharactersForLayoutTesting then secondResultNameWithEnoughCharactersForLayoutTesting else fallbackResultNameWithEnoughCharactersForLayoutTesting\n"
  let expected :=
    "def elseIfChain : Result :=\n"
    ++ "  if conditionNameWithEnoughCharactersForLayoutTesting then\n"
    ++ "    firstResultNameWithEnoughCharactersForLayoutTesting\n"
    ++ "  else if secondConditionNameWithEnoughCharactersForLayoutTesting then\n"
    ++ "    secondResultNameWithEnoughCharactersForLayoutTesting\n"
    ++ "  else\n"
    ++ "    fallbackResultNameWithEnoughCharactersForLayoutTesting\n"
  let formatted ← Formatter.formatSourceWithEnv env source "else-if-chain.lean"
  assertEq "else-if continues on else line" expected formatted

def assertTermMatchAlternativesStayOnOwnLines (env : Lean.Environment) : IO Unit := do
  let source :=
    "def lookupVariableValue? : Option InputValue :=\n"
    ++ "  match variableValues with\n"
    ++ "  | [] => none\n"
    ++ "  | (variableName, value) :: rest => value\n"
  let formatted ←
    Formatter.formatSourceWithEnv env source "term-match-alternatives.lean"
  assertEq "term match alternatives stay on own lines" source formatted

def assertLetMatchAlternativesAlign (env : Lean.Environment) : IO Unit := do
  let source :=
    "def letMatchRhs : Result :=\n"
    ++ "  let current :=\n"
    ++ "    match selection with\n"
    ++ "    | .field responseName fieldName arguments _directives selectionSet =>\n"
    ++ "        collectFields schema parentType selectionSet\n"
    ++ "    | .inlineFragment none _directives selectionSet =>\n"
    ++ "        collectFields schema parentType selectionSet\n"
    ++ "  current\n"
  let formatted ← Formatter.formatSourceWithEnv env source "let-match-alternatives.lean"
  assertEq "let match alternatives align" source formatted

def assertMatchArmPreservesSourceBreakBeforeShortRhs (env : Lean.Environment)
    : IO Unit := do
  let source := "def shortMatch : Nat -> Nat\n" ++ "  | x =>\n" ++ "      x\n"
  let formatted ←
    Formatter.formatSourceWithEnv env source "match-arm-ignore-source-break.lean"
  assertEq "match arm preserves source break before short rhs" source formatted

def assertIfThenElseBreaksBalanced (env : Lean.Environment) : IO Unit := do
  let source :=
    "def balancedIfThenElse : Result := if fieldResponseName == responseName then some response else lookupResponseField? responseName rest\n"
  let expected :=
    "def balancedIfThenElse : Result :=\n"
    ++ "  if fieldResponseName == responseName then\n"
    ++ "    some response\n"
    ++ "  else\n"
    ++ "    lookupResponseField? responseName rest\n"
  let formatted ← Formatter.formatSourceWithEnv env source "if-then-else-balanced.lean"
  assertEq "if-then-else balanced breaks" expected formatted

def assertParenthesizedIfAlignsBeforeBranchIndent (env : Lean.Environment)
    : IO Unit := do
  let source :=
    "def diagnosticExit : UInt32 :=\n"
    ++ "  pure\n"
    ++ "    (if buildExit == 0 && commentExit == 0 && styleExit == 0 && leanExit == 0 then\n"
    ++ "      0\n"
    ++ "      else\n"
    ++ "      1)\n"
  let expected :=
    "def diagnosticExit : UInt32 :=\n"
    ++ "  pure\n"
    ++ "    ( if buildExit == 0 && commentExit == 0 && styleExit == 0 && leanExit == 0 then\n"
    ++ "        0\n"
    ++ "      else\n"
    ++ "        1)\n"
  let formatted ←
    Formatter.formatSourceWithEnv env source "parenthesized-if-alignment.lean"
  assertEq "parenthesized if aligns before branch indentation" expected formatted

def assertMatchArmRhsIndent (env : Lean.Environment) : IO Unit := do
  let source :=
    "def responseName? : Selection -> Option Name\n"
    ++ "  | .field responseName _fieldName _arguments _directives _selectionSet =>\n"
    ++ "      some responseName\n"
    ++ "  | _ => none\n"
  let formatted ← Formatter.formatSourceWithEnv env source "match-arm-rhs-indent.lean"
  assertEq "match arm RHS indentation" source formatted

def assertMatchArmPatternsHonorSourceBreaks (env : Lean.Environment) : IO Unit := do
  let source :=
    "def collectSelection (schema : Schema) (variableValues : VariableValues)\n"
    ++ "    : Name -> ResolverValue ObjectRef -> Selection -> List (Name × List ExecutableField)\n"
    ++ "  | parentType, _source,\n"
    ++ "    .field responseName fieldName arguments directives selectionSet =>\n"
    ++ "      body\n"
  let expected :=
    "def collectSelection (schema : Schema) (variableValues : VariableValues)\n"
    ++ "    : Name -> ResolverValue ObjectRef -> Selection -> List (Name × List ExecutableField)\n"
    ++ "  | parentType,\n"
    ++ "    _source,\n"
    ++ "    .field responseName fieldName arguments directives selectionSet =>\n"
    ++ "      body\n"
  let formatted ←
    Formatter.formatSourceWithEnv env source "match-arm-pattern-source-breaks.lean"
  assertEq "match arm patterns honor balanced source breaks" expected formatted

def assertMatchArmPatternsBreakBalanced (env : Lean.Environment) : IO Unit := do
  let source :=
    "def collect : First -> Second -> Third -> Result\n"
    ++ "  | first, second,\n"
    ++ "    third => body\n"
  let expected :=
    "def collect : First -> Second -> Third -> Result\n"
    ++ "  | first,\n"
    ++ "    second,\n"
    ++ "    third => body\n"
  let formatted ←
    Formatter.formatSourceWithEnv env source "match-arm-patterns-balanced.lean"
  assertEq "match arm pattern source breaks activate balanced peers" expected formatted

def assertMatchDiscriminantsFlowAfterCommas (env : Lean.Environment) : IO Unit := do
  let source :=
    "def compare segment index :=\n"
    ++ "  match defaultPresentChildIndexBefore? segment index, defaultPresentChildIndexAfter? segment index, defaultPresentChildIndexAround? segment index with\n"
    ++ "  | some before, some after,\n"
    ++ "    some around => result\n"
  let expected :=
    "def compare segment index :=\n"
    ++ "  match defaultPresentChildIndexBefore? segment index,\n"
    ++ "        defaultPresentChildIndexAfter? segment index,\n"
    ++ "        defaultPresentChildIndexAround? segment index with\n"
    ++ "  | some before,\n"
    ++ "    some after,\n"
    ++ "    some around => result\n"
  let formatted ←
    Formatter.formatSourceWithEnv env source "match-discriminants-flow.lean"
  assertEq "match discriminants flow after commas aligned under first" expected
    formatted

def assertMatchPeerBreakConsistency (env : Lean.Environment) : IO Unit := do
  assertMatchArmPatternsHonorSourceBreaks env
  assertMatchArmPatternsBreakBalanced env
  assertMatchDiscriminantsFlowAfterCommas env

def assertMatchDiscriminantApplicationIndent (env : Lean.Environment) : IO Unit := do
  let source :=
    "def longMatchDiscriminant (child : Nat) (children : List Nat) : Nat :=\n"
    ++ "  match veryLongFunctionName child children additionalArgumentOne\n"
    ++ "          additionalArgumentTwo with\n"
    ++ "  | [] => 0\n"
    ++ "  | _ :: rest => rest.length\n"
  let formatted ←
    Formatter.formatSourceWithEnv env
      source "match-discriminant-application-indent.lean"
  assertEq "match discriminant application indentation" source formatted

def assertNestedTermMatchAlternativesAlign (env : Lean.Environment) : IO Unit := do
  let source :=
    "def allowsBool : DirectiveApplication -> Bool\n"
    ++ "  | .skip ifArgument =>\n"
    ++ "      match ifArgument.staticBoolean? with\n"
    ++ "      | some value => !value\n"
    ++ "      | none => false\n"
    ++ "  | .include ifArgument => true\n"
  let formatted ←
    Formatter.formatSourceWithEnv env source "nested-term-match-alternatives.lean"
  assertEq "nested term match alternatives align" source formatted

def assertNestedMatchAfterLambdaAlignsWithMatch (env : Lean.Environment) : IO Unit := do
  let source :=
    "def letIfRhs : Result :=\n"
    ++ "  let normalizedSubselections :=\n"
    ++ "    if objectTypeNameBool schema returnType then\n"
    ++ "      normalizeSelectionSet schema returnType mergedSubselections\n"
    ++ "    else\n"
    ++ "      (schema.getPossibleTypes returnType).filterMap\n"
    ++ "        (fun objectType =>\n"
    ++ "          match normalizeSelectionSet schema objectType mergedSubselections with\n"
    ++ "        | [] => none\n"
    ++ "        | selection :: rest =>\n"
    ++ "            some (.inlineFragment (some objectType) [] (selection :: rest)))\n"
    ++ "  normalizedSubselections\n"
  let expected :=
    "def letIfRhs : Result :=\n"
    ++ "  let normalizedSubselections :=\n"
    ++ "    if objectTypeNameBool schema returnType then\n"
    ++ "      normalizeSelectionSet schema returnType mergedSubselections\n"
    ++ "    else\n"
    ++ "      (schema.getPossibleTypes returnType).filterMap\n"
    ++ "        (fun objectType =>\n"
    ++ "          match normalizeSelectionSet schema objectType mergedSubselections with\n"
    ++ "          | [] => none\n"
    ++ "          | selection :: rest =>\n"
    ++ "              some (.inlineFragment (some objectType) [] (selection :: rest)))\n"
    ++ "  normalizedSubselections\n"
  let formatted ←
    Formatter.formatSourceWithEnv env source "nested-match-after-lambda-aligns.lean"
  assertEq "nested match after lambda aligns with match" expected formatted

def assertPrefixedMatchAlternativesAlignWithMatch (env : Lean.Environment)
    : IO Unit := do
  let source :=
    "def nestedOptionMatchInListMatch (selectionSet : List Nat) (field? : Option Nat) : Prop :=\n"
    ++ "  match selectionSet with\n"
    ++ "  | [] => True\n"
    ++ "  | _ :: _ =>\n"
    ++ "      condition\n"
    ++ "      -> match field? with\n"
    ++ "      | none => False\n"
    ++ "      | some fieldDefinition => True\n"
  let expected :=
    "def nestedOptionMatchInListMatch (selectionSet : List Nat) (field? : Option Nat)\n"
    ++ "    : Prop :=\n"
    ++ "  match selectionSet with\n"
    ++ "  | [] => True\n"
    ++ "  | _ :: _ =>\n"
    ++ "      condition\n"
    ++ "      -> match field? with\n"
    ++ "          | none => False\n"
    ++ "          | some fieldDefinition => True\n"
  let formatted ←
    Formatter.formatSourceWithEnv env source "prefixed-match-alternatives-align.lean"
  assertEq "prefixed match alternatives align with match" expected formatted

def assertLambdaBodyUsesOperandAnchor (env : Lean.Environment) : IO Unit := do
  let source :=
    "def logicalMatchOperandAnchor : Bool :=\n"
    ++ "  (interfaceName == targetName)\n"
    ++ "  || match schema.lookupInterface interfaceName with\n"
    ++ "      | some interfaceType =>\n"
    ++ "          interfaceType.interfaces.any\n"
    ++ "            (fun parentName =>\n"
    ++ "          interfaceTypeImplementsInterfaceBoundedBool schema bound parentName targetName)\n"
    ++ "      | none => false\n"
  let expected :=
    "def logicalMatchOperandAnchor : Bool :=\n"
    ++ "  (interfaceName == targetName)\n"
    ++ "  || match schema.lookupInterface interfaceName with\n"
    ++ "      | some interfaceType =>\n"
    ++ "          interfaceType.interfaces.any\n"
    ++ "            (fun parentName =>\n"
    ++ "              interfaceTypeImplementsInterfaceBoundedBool schema bound parentName\n"
    ++ "                targetName)\n"
    ++ "      | none => false\n"
  let formatted ←
    Formatter.formatSourceWithEnv env source "lambda-body-operand-anchor.lean"
  assertEq "lambda body uses operand anchor" expected formatted

def assertLambdaBinderSequenceBreaksBetweenBinders (env : Lean.Environment)
    : IO Unit := do
  let source :=
    "def foldValues values :=\n"
    ++ "  values.foldl\n"
    ++ "    (fun (state : List Execution.ResponseValue × List Execution.ResponseValue) incomingValue =>\n"
    ++ "      state)\n"
    ++ "    ([], [])\n"
  let expected :=
    "def foldValues values :=\n"
    ++ "  values.foldl\n"
    ++ "    (fun (state : List Execution.ResponseValue × List Execution.ResponseValue)\n"
    ++ "        incomingValue =>\n"
    ++ "      state)\n"
    ++ "    ([], [])\n"
  let formatted ← Formatter.formatSourceWithEnv env source "lambda-binder-sequence.lean"
  assertEq "lambda binder sequence breaks between binders" expected formatted
  let moduleTree ←
    SyntaxTree.parseModuleStringWithEnv env formatted "lambda-binder-sequence.lean"
  assertTrue "lambda binder sequence has no overflow"
    (Formatter.Diagnostics.overflowOccurrences moduleTree).isEmpty

def assertQuantifierBreaksAfterComma (env : Lean.Environment) : IO Unit := do
  let source :=
    "def quantifierCommaBreak : Prop := ∀ scopedField, scopedField ∈ sourceFieldsWithEnoughCharactersForLayoutTestingAndMoreText -> targetField ∈ targetFields\n"
  let expected :=
    "def quantifierCommaBreak : Prop :=\n"
    ++ "  ∀ scopedField,\n"
    ++ "    scopedField ∈ sourceFieldsWithEnoughCharactersForLayoutTestingAndMoreText\n"
    ++ "    -> targetField ∈ targetFields\n"
  let formatted ← Formatter.formatSourceWithEnv env source "quantifier-comma-break.lean"
  assertEq "quantifier breaks after comma" expected formatted

def assertQuantifierIdentifierSequenceFlows (env : Lean.Environment) : IO Unit := do
  let source :=
    "def quantifiedPrefixes : Prop := ∃ leftPrefixFields leftPrefixErrors "
    ++ "rightPrefixFields rightPrefixErrors leftSuffixFields leftSuffixErrors "
    ++ "rightSuffixFields rightSuffixErrors, True\n"
  let expected :=
    "def quantifiedPrefixes : Prop :=\n"
    ++ "  ∃ leftPrefixFields leftPrefixErrors rightPrefixFields rightPrefixErrors\n"
    ++ "      leftSuffixFields leftSuffixErrors rightSuffixFields rightSuffixErrors,\n"
    ++ "    True\n"
  let formatted ←
    Formatter.formatSourceWithEnv env source "quantifier-identifier-sequence.lean"
  assertEq "quantifier identifier sequence flows" expected formatted
  let moduleTree ←
    SyntaxTree.parseModuleStringWithEnv env formatted
      "quantifier-identifier-sequence.lean"
  assertTrue "quantifier identifier sequence has no overflow"
    (Formatter.Diagnostics.overflowOccurrences moduleTree).isEmpty

def assertCheckCommandHasRule (env : Lean.Environment) : IO Unit := do
  let fittingSource :=
    "#check CompleteNormalization.completeNormalizeOperation_uniqueUpToReordering\n"
  let moduleTree ←
    SyntaxTree.parseModuleStringWithEnv env fittingSource "check-command.lean"
  assertTrue "check command has complete rule coverage"
    (Formatter.Diagnostics.missingRuleOccurrencesForModule moduleTree).isEmpty
  let fittingFormatted ←
    Formatter.formatSourceWithEnv env fittingSource "check-command.lean"
  assertEq "fitting check command stays flat" fittingSource fittingFormatted
  let overflowingSource :=
    "#check CompleteNormalization."
    ++ "completeNormalizeOperation_uniqueUpToReorderingWithAdditionalLayoutText\n"
  let overflowingFormatted ←
    Formatter.formatSourceWithEnv env overflowingSource "long-check-command.lean"
  let expected :=
    "#check\n"
    ++ "  CompleteNormalization."
    ++ "completeNormalizeOperation_uniqueUpToReorderingWithAdditionalLayoutText\n"
  assertEq "overflowing check command breaks after check" expected overflowingFormatted

def assertArrowQuantifierKeepsQuantifierOnArrowLine (env : Lean.Environment)
    : IO Unit := do
  let source :=
    "def arrowQuantifierOperand : Prop := (left.parentType = right.parentType ∨ ¬ schema.objectType left.parentType ∨ ¬ schema.objectType right.parentType) -> ∀ objectType, FieldsInSetCanMerge schema objectType (left.selectionSet ++ right.selectionSet)\n"
  let expected :=
    "def arrowQuantifierOperand : Prop :=\n"
    ++ "  (left.parentType = right.parentType\n"
    ++ "    ∨ ¬ schema.objectType left.parentType\n"
    ++ "    ∨ ¬ schema.objectType right.parentType)\n"
    ++ "  -> ∀ objectType,\n"
    ++ "      FieldsInSetCanMerge schema objectType (left.selectionSet ++ right.selectionSet)\n"
  let formatted ←
    Formatter.formatSourceWithEnv env source "arrow-quantifier-operand.lean"
  assertEq "arrow quantifier keeps quantifier on arrow line" expected formatted

def assertArrowMatchKeepsMatchOnArrowLine (env : Lean.Environment) : IO Unit := do
  let source :=
    "def arrowMatchOperand : Prop :=\n"
    ++ "  directivesAllowIn boolCase directives = true\n"
    ++ "  ->\n"
    ++ "    match selectionSet with\n"
    ++ "    | [] => True\n"
    ++ "    | _ :: _ => typeConditionStackFeasible schema typeConditions\n"
  let expected :=
    "def arrowMatchOperand : Prop :=\n"
    ++ "  directivesAllowIn boolCase directives = true\n"
    ++ "  -> match selectionSet with\n"
    ++ "      | [] => True\n"
    ++ "      | _ :: _ => typeConditionStackFeasible schema typeConditions\n"
  let formatted ← Formatter.formatSourceWithEnv env source "arrow-match-operand.lean"
  assertEq "arrow match keeps match on arrow line" expected formatted

def assertArrowMatchInMatchAltIdempotent (env : Lean.Environment) : IO Unit := do
  let source :=
    "def arrowMatchInAlt : Selection -> Prop\n"
    ++ "  | .field _responseName fieldName _arguments directives selectionSet =>\n"
    ++ "      directivesAllowIn boolCase directives = true ->\n"
    ++ "        match selectionSet with\n"
    ++ "        | [] => True\n"
    ++ "        | _ :: _ => typeConditionStackFeasible schema typeConditions\n"
  let expected :=
    "def arrowMatchInAlt : Selection -> Prop\n"
    ++ "  | .field _responseName fieldName _arguments directives selectionSet =>\n"
    ++ "      directivesAllowIn boolCase directives = true\n"
    ++ "      -> match selectionSet with\n"
    ++ "          | [] => True\n"
    ++ "          | _ :: _ => typeConditionStackFeasible schema typeConditions\n"
  let once ← Formatter.formatSourceWithEnv env source "arrow-match-alt.lean"
  assertEq "arrow match in match alternative formats in one pass" expected once
  let twice ← Formatter.formatSourceWithEnv env once "arrow-match-alt.lean"
  assertEq "arrow match in match alternative idempotence" once twice

def assertQuantifierBinderSequenceBreaksBetweenBinders (env : Lean.Environment)
    : IO Unit := do
  let source :=
    "def quantifierBinderSequence : Prop := SchemaWellFormedness.schemaWellFormed schema -> Validation.operationDefinitionValid schema operation -> ∀ {ObjectRef : Type} (resolvers : Resolvers ObjectRef) variableValues fuel (source : ResolverValue ObjectRef), NormalForm.operationBoolVarsComplete operation variableValues\n"
  let expected :=
    "def quantifierBinderSequence : Prop :=\n"
    ++ "  SchemaWellFormedness.schemaWellFormed schema\n"
    ++ "  -> Validation.operationDefinitionValid schema operation\n"
    ++ "  -> ∀ {ObjectRef : Type} (resolvers : Resolvers ObjectRef) variableValues fuel\n"
    ++ "        (source : ResolverValue ObjectRef),\n"
    ++ "      NormalForm.operationBoolVarsComplete operation variableValues\n"
  let formatted ←
    Formatter.formatSourceWithEnv env source "quantifier-binder-sequence-break.lean"
  assertEq "quantifier binder sequence breaks between binders" expected formatted

def assertInductiveConstructorIndentation (env : Lean.Environment) : IO Unit := do
  let source :=
    "inductive ConstructorBinderLayout where\n"
    ++ "  | intro (hknown : ∀ name value, (name, value) ∈ fields -> (Schema.lookupArgumentDefinition definitions name).isSome = true) : ConstructorBinderLayout\n"
    ++ "\n"
    ++ "inductive ConstructorResultLayout where\n"
    ++ "  | intro (fields : List Field) : ConstructorResultLayoutForInput schema (ConstructorValue.object fields) (TypeRef.named typeName)\n"
    ++ "\n"
    ++ "inductive ConstructorLetHypothesis where\n"
    ++ "  | intro (hfields : let fields := collectFields schema parentType selectionSet\n"
    ++ "    ∀ left, left ∈ fields -> ∀ right, right ∈ fields -> left.responseName = right.responseName -> FieldsForNameCanMerge schema left right) : ConstructorLetHypothesis\n"
  let expected :=
    "inductive ConstructorBinderLayout where\n"
    ++ "  | intro\n"
    ++ "    (hknown\n"
    ++ "      : ∀ name value,\n"
    ++ "          (name, value) ∈ fields\n"
    ++ "          -> (Schema.lookupArgumentDefinition definitions name).isSome = true)\n"
    ++ "    : ConstructorBinderLayout\n"
    ++ "\n"
    ++ "inductive ConstructorResultLayout where\n"
    ++ "  | intro (fields : List Field)\n"
    ++ "    : ConstructorResultLayoutForInput schema (ConstructorValue.object fields)\n"
    ++ "        (TypeRef.named typeName)\n"
    ++ "\n"
    ++ "inductive ConstructorLetHypothesis where\n"
    ++ "  | intro\n"
    ++ "    (hfields\n"
    ++ "      : let fields := collectFields schema parentType selectionSet\n"
    ++ "        ∀ left,\n"
    ++ "          left ∈ fields\n"
    ++ "          -> ∀ right,\n"
    ++ "              right ∈ fields\n"
    ++ "              -> left.responseName = right.responseName\n"
    ++ "              -> FieldsForNameCanMerge schema left right)\n"
    ++ "    : ConstructorLetHypothesis\n"
  let formatted ←
    Formatter.formatSourceWithEnv env source "inductive-constructor-indent.lean"
  assertEq "inductive constructor indentation" expected formatted

def assertConstructorBinderContinuesFromUnbrokenPrefix (env : Lean.Environment)
    : IO Unit := do
  let source :=
    "inductive ConstructorBinderLayout (schema : Schema) : List Definition -> List Field -> Prop where\n"
    ++ "  | intro (definitions : List Definition) (fields : List Field) (hnodup : fields.Nodup) (hknown : ∀ name value, (name, value) ∈ fields -> (Schema.lookupArgumentDefinition definitions name).isSome = true)\n"
  let expected :=
    "inductive ConstructorBinderLayout (schema : Schema)\n"
    ++ "    : List Definition -> List Field -> Prop where\n"
    ++ "  | intro (definitions : List Definition) (fields : List Field) (hnodup : fields.Nodup)\n"
    ++ "    (hknown\n"
    ++ "      : ∀ name value,\n"
    ++ "          (name, value) ∈ fields\n"
    ++ "          -> (Schema.lookupArgumentDefinition definitions name).isSome = true)\n"
  let formatted ←
    Formatter.formatSourceWithEnv env source "constructor-binder-unbroken-prefix.lean"
  assertEq "constructor binder continues from unbroken prefix" expected formatted

def assertStructureFieldsBreakMandatory (env : Lean.Environment) : IO Unit := do
  let source := "structure Point where\n" ++ "  x : Nat\n" ++ "  y : Nat\n"
  let expected := "structure Point where\n" ++ "  x : Nat\n" ++ "  y : Nat\n"
  let formatted ← Formatter.formatSourceWithEnv env source "structure-fields-break.lean"
  assertEq "structure fields break mandatory" expected formatted

def assertStructureFieldTypeBreakIndentation (env : Lean.Environment) : IO Unit := do
  let source :=
    "structure ResolverFixture (ObjectRef : Type := PUnit) where\n"
    ++ "  resolve : Name -> Name -> List Argument -> ResolverValue ObjectRef -> Option (ResolverValue ObjectRef)\n"
  let expected :=
    "structure ResolverFixture (ObjectRef : Type := PUnit) where\n"
    ++ "  resolve\n"
    ++ "    : Name -> Name -> List Argument -> ResolverValue ObjectRef\n"
    ++ "      -> Option (ResolverValue ObjectRef)\n"
  let formatted ←
    Formatter.formatSourceWithEnv env source "structure-field-type-break-indent.lean"
  assertEq "structure field type break indentation" expected formatted

def assertInductiveAlternativesBreakMandatory (env : Lean.Environment) : IO Unit := do
  let source := "inductive Color where | red | green | blue\n"
  let expected :=
    "inductive Color where\n" ++ "  | red\n" ++ "  | green\n" ++ "  | blue\n"
  let formatted ←
    Formatter.formatSourceWithEnv env source "inductive-alternatives-break.lean"
  assertEq "inductive alternatives break mandatory" expected formatted

def assertStructInstanceFieldsBreakMandatory (env : Lean.Environment) : IO Unit := do
  let source :=
    "def recordOperand :=\n"
    ++ "  { parentType := validParent\n"
    ++ "    responseName := responseName }\n"
  let expected :=
    "def recordOperand :=\n"
    ++ "  {\n"
    ++ "    parentType := validParent\n"
    ++ "    responseName := responseName\n"
    ++ "  }\n"
  let formatted ←
    Formatter.formatSourceWithEnv env source "struct-instance-fields-break.lean"
  assertEq "structure constructor fields break mandatory" expected formatted

def assertStructInstanceFieldsBreakMandatoryBetweenFields (env : Lean.Environment)
    : IO Unit := do
  let source :=
    "def recordOperand :=\n"
    ++ "  { first := one,\n"
    ++ "    second := two\n"
    ++ "    third := three }\n"
  let expected :=
    "def recordOperand :=\n"
    ++ "  {\n"
    ++ "    first := one,\n"
    ++ "    second := two\n"
    ++ "    third := three\n"
    ++ "  }\n"
  let formatted ←
    Formatter.formatSourceWithEnv env source
      "struct-instance-fields-missing-comma-between.lean"
  assertEq "structure constructor fields break mandatory between fields" expected
    formatted

def assertStructInstanceFieldsBreakBalanced (env : Lean.Environment) : IO Unit := do
  let source :=
    "def recordOperand := { parentType := validParentWithEnoughCharactersForLayoutTesting, responseName := responseNameWithEnoughCharactersForLayoutTesting }\n"
  let expected :=
    "def recordOperand :=\n"
    ++ "  {\n"
    ++ "    parentType := validParentWithEnoughCharactersForLayoutTesting,\n"
    ++ "    responseName := responseNameWithEnoughCharactersForLayoutTesting\n"
    ++ "  }\n"
  let formatted ←
    Formatter.formatSourceWithEnv env source "struct-instance-fields-balanced.lean"
  assertEq "structure constructor fields break balanced" expected formatted

def assertTypedStructInstanceBreaksBalanced (env : Lean.Environment) : IO Unit := do
  let source :=
    "def responseWitness : Prop := response = ({ data := exceptionallyLongResponseObjectConstructorNameUsedToForceBalancedStructureLayout rightFields, errors := rightErrors }\n"
    ++ "  : Execution.Response)\n"
  let expected :=
    "def responseWitness : Prop :=\n"
    ++ "  response\n"
    ++ "  = ({\n"
    ++ "        data :=\n"
    ++ "          exceptionallyLongResponseObjectConstructorNameUsedToForceBalancedStructureLayout\n"
    ++ "            rightFields,\n"
    ++ "        errors := rightErrors\n"
    ++ "      }\n"
    ++ "      : Execution.Response)\n"
  let formatted ←
    Formatter.formatSourceWithEnv env source "typed-struct-instance-balanced.lean"
  assertEq "typed structure constructor breaks braces and keeps ascribed type together"
    expected formatted

def assertStructInstanceFieldBindersPreserved (env : Lean.Environment) : IO Unit := do
  let source :=
    "instance : Coe Nat Nat where\n"
    ++ "  coe value := value\n"
    ++ "\n"
    ++ "instance : Coe Nat Nat where\n"
    ++ "  coe (value : Nat) := value\n"
  let formatted ←
    Formatter.formatSourceWithEnv env source "struct-instance-field-binders.lean"
  assertTrue "structure field binders preserve code"
    (← codePreservedIgnoringWhitespace env source formatted)
  assertTextContains "single structure field binder is preserved"
    formatted "coe value := value"
  assertTextContains "typed structure field binder is preserved"
    formatted "coe (value : Nat) := value"

def assertStructUpdateWithFieldsBreaks (env : Lean.Environment) : IO Unit := do
  let shortSource := "def update state := { state with output := text }\n"
  let shortFormatted ←
    Formatter.formatSourceWithEnv env shortSource "struct-update-short.lean"
  assertEq "short structure update stays flat" shortSource shortFormatted

  let source :=
    "def normalizeOperation (schema : Schema) (operation : Operation) : Operation :=\n"
    ++ "  { operation with selectionSet := normalizeSelectionSet schema operation.rootType operation.selectionSet }\n"
  let expected :=
    "def normalizeOperation (schema : Schema) (operation : Operation) : Operation :=\n"
    ++ "  {\n"
    ++ "    operation with\n"
    ++ "      selectionSet :=\n"
    ++ "        normalizeSelectionSet schema operation.rootType operation.selectionSet\n"
    ++ "  }\n"
  let formatted ←
    Formatter.formatSourceWithEnv env source "struct-update-fields-break.lean"
  assertEq "structure update fields break" expected formatted

  let applicationSource :=
    "def updateFromApplication : State :=\n"
    ++ "  { veryLongStateBuilderNameForStructureUpdate firstArgumentForStructureUpdate secondArgumentForStructureUpdate thirdArgumentForStructureUpdate with output := text }\n"
  let applicationExpected :=
    "def updateFromApplication : State :=\n"
    ++ "  {\n"
    ++ "    veryLongStateBuilderNameForStructureUpdate firstArgumentForStructureUpdate\n"
    ++ "        secondArgumentForStructureUpdate thirdArgumentForStructureUpdate with\n"
    ++ "      output := text\n"
    ++ "  }\n"
  let applicationFormatted ←
    Formatter.formatSourceWithEnv env applicationSource
      "struct-update-application-source.lean"
  assertEq "structure update flows an overflowing application source"
    applicationExpected applicationFormatted
  let applicationFormattedAgain ←
    Formatter.formatSourceWithEnv env applicationFormatted
      "struct-update-application-source.lean"
  assertEq "overflowing structure-update source is idempotent" applicationFormatted
    applicationFormattedAgain

  let infixSource :=
    "def updateEquality : Prop :=\n"
    ++ "  { state with veryLongFieldNameForStructureUpdate := veryLongFunctionNameForStructureUpdate firstArgumentForStructureUpdate secondArgumentForStructureUpdate thirdArgumentForStructureUpdate } = expectedState\n"
  let infixExpected :=
    "def updateEquality : Prop :=\n"
    ++ "  {\n"
    ++ "      state with\n"
    ++ "        veryLongFieldNameForStructureUpdate :=\n"
    ++ "          veryLongFunctionNameForStructureUpdate firstArgumentForStructureUpdate\n"
    ++ "            secondArgumentForStructureUpdate thirdArgumentForStructureUpdate\n"
    ++ "    }\n"
    ++ "  = expectedState\n"
  let infixFormatted ←
    Formatter.formatSourceWithEnv env infixSource "struct-update-infix-depth.lean"
  assertEq "structure update source uses infix-left depth" infixExpected infixFormatted

def assertTupleBreakBalanced (env : Lean.Environment) : IO Unit := do
  let source :=
    "def tupleOperand := (firstItemNameWithEnoughCharactersForLayoutTesting, secondItemNameWithEnoughCharactersForLayoutTesting,)\n"
  let expected :=
    "def tupleOperand :=\n"
    ++ "  (\n"
    ++ "    firstItemNameWithEnoughCharactersForLayoutTesting,\n"
    ++ "    secondItemNameWithEnoughCharactersForLayoutTesting,\n"
    ++ "  )\n"
  let formatted ← Formatter.formatSourceWithEnv env source "tuple-balanced.lean"
  assertEq "tuple breaks balanced" expected formatted

def assertAnonymousConstructorBreakBalanced (env : Lean.Environment) : IO Unit := do
  let fittingSource := "def shortConstructor := ⟨left, right⟩\n"
  let fittingFormatted ←
    Formatter.formatSourceWithEnv env fittingSource "anonymous-constructor-fitting.lean"
  assertEq "fitting anonymous constructor stays flat" fittingSource fittingFormatted
  let source :=
    "def anonymousCtorOperand := ⟨firstItemNameWithEnoughCharactersForLayoutTesting, secondItemNameWithEnoughCharactersForLayoutTesting, thirdItemNameWithEnoughCharactersForLayoutTesting⟩\n"
  let expected :=
    "def anonymousCtorOperand :=\n"
    ++ "  ⟨\n"
    ++ "    firstItemNameWithEnoughCharactersForLayoutTesting,\n"
    ++ "    secondItemNameWithEnoughCharactersForLayoutTesting,\n"
    ++ "    thirdItemNameWithEnoughCharactersForLayoutTesting\n"
    ++ "  ⟩\n"
  let formatted ←
    Formatter.formatSourceWithEnv env source "anonymous-constructor-balanced.lean"
  assertEq "anonymous constructor breaks balanced" expected formatted
  match Formatter.LineBreakRules.ruleFor
          (SyntaxTree.Tree.node (.raw `Lean.Parser.Term.anonymousCtor) #[]) with
  | some rule =>
      assertEq "anonymous constructor uses dedicated rule" "anonymousCtor" rule.name
  | none => throw <| IO.userError "anonymous constructor has no rule"
  let setoidSource :=
    "def stronglyConnectedSetoid : Setoid V :=\n"
    ++ "  ⟨fun a b => (Nonempty (Path a b)) ∧ (Nonempty (Path b a)), fun _ => ⟨⟨Path.nil⟩, ⟨Path.nil⟩⟩, fun ⟨hab, hba⟩ => ⟨hba, hab⟩, fun ⟨hab, hba⟩ ⟨hbc, hcb⟩ => ⟨⟨hab.some.comp hbc.some⟩, ⟨hcb.some.comp hba.some⟩⟩⟩\n"
  let setoidExpected :=
    "def stronglyConnectedSetoid : Setoid V :=\n"
    ++ "  ⟨\n"
    ++ "    fun a b => (Nonempty (Path a b)) ∧ (Nonempty (Path b a)),\n"
    ++ "    fun _ => ⟨⟨Path.nil⟩, ⟨Path.nil⟩⟩,\n"
    ++ "    fun ⟨hab, hba⟩ => ⟨hba, hab⟩,\n"
    ++ "    fun ⟨hab, hba⟩ ⟨hbc, hcb⟩ => ⟨⟨hab.some.comp hbc.some⟩, ⟨hcb.some.comp hba.some⟩⟩\n"
    ++ "  ⟩\n"
  let setoidFormatted ←
    Formatter.formatSourceWithEnv env setoidSource "anonymous-constructor-setoid.lean"
  assertEq "mathlib-style anonymous constructor breaks balanced"
    setoidExpected setoidFormatted
  let moduleTree ←
    SyntaxTree.parseModuleStringWithEnv env setoidFormatted
      "anonymous-constructor-setoid-formatted.lean"
  assertTrue "mathlib-style anonymous constructor has no overflow"
    (Formatter.Diagnostics.overflowOccurrences moduleTree).isEmpty

def assertExportBreaksLongList (env : Lean.Environment) : IO Unit := do
  let source :=
    "export CompleteNormalization (\n"
    ++ "  BoolVar\n"
    ++ "  BoolCase\n"
    ++ "  inputValueBooleanVariables\n"
    ++ "  inputValuesBooleanVariables\n"
    ++ "  inputObjectFieldsBooleanVariables\n"
    ++ "  directiveBooleanVariables\n"
    ++ "  directivesBooleanVariables\n"
    ++ "  selectionBooleanVariables\n"
    ++ "  selectionSetBooleanVariables\n"
    ++ "  boolVariableMem\n"
    ++ "  dedupBoolVars\n"
    ++ "  allBoolCases\n"
    ++ "  BoolCase.lookup?\n"
    ++ "  inputValueBoolIn?\n"
    ++ "  directiveAllowsIn\n"
    ++ "  directivesAllowIn\n"
    ++ "  directiveForBit\n"
    ++ "  wrapWithBoolCase\n"
    ++ "  filterSelectionSetBoolCase\n"
    ++ "  normalizeBoolCaseForType\n"
    ++ "  completeNormalizeRootSelectionSet\n"
    ++ "  completeNormalizeOperation\n"
    ++ "  operationBoolVars\n"
    ++ ")\n"
  let expected :=
    "export CompleteNormalization (\n"
    ++ "  BoolVar\n"
    ++ "  BoolCase\n"
    ++ "  inputValueBooleanVariables\n"
    ++ "  inputValuesBooleanVariables\n"
    ++ "  inputObjectFieldsBooleanVariables\n"
    ++ "  directiveBooleanVariables\n"
    ++ "  directivesBooleanVariables\n"
    ++ "  selectionBooleanVariables\n"
    ++ "  selectionSetBooleanVariables\n"
    ++ "  boolVariableMem\n"
    ++ "  dedupBoolVars\n"
    ++ "  allBoolCases\n"
    ++ "  BoolCase.lookup?\n"
    ++ "  inputValueBoolIn?\n"
    ++ "  directiveAllowsIn\n"
    ++ "  directivesAllowIn\n"
    ++ "  directiveForBit\n"
    ++ "  wrapWithBoolCase\n"
    ++ "  filterSelectionSetBoolCase\n"
    ++ "  normalizeBoolCaseForType\n"
    ++ "  completeNormalizeRootSelectionSet\n"
    ++ "  completeNormalizeOperation\n"
    ++ "  operationBoolVars\n"
    ++ ")\n"
  let formatted ← Formatter.formatSourceWithEnv env source "export-long-list.lean"
  assertEq "export breaks long list" expected formatted

def assertBangApplicationDiagnostics (env : Lean.Environment) : IO Unit := do
  let allowed := "def x := ! f a b\n"
  let allowedTree ← SyntaxTree.parseModuleStringWithEnv env allowed "bang-allowed.lean"
  assertTrue "allowed bang has no diagnostic"
    (Formatter.Diagnostics.diagnosticsForModule allowedTree).isEmpty
  let warned := "def x := !f a b\n"
  let warnedTree ← SyntaxTree.parseModuleStringWithEnv env warned "bang-warned.lean"
  match Formatter.Diagnostics.diagnosticsForModule warnedTree with
  | [diagnostic] =>
      assertTrue "compact bang diagnostic kind"
        (diagnostic.kind == Formatter.Diagnostics.DiagnosticKind.compactBangApplication)
  | diagnostics =>
      throw <| IO.userError s!"expected one bang diagnostic, got {repr diagnostics}"

def assertCliParsing : IO Unit := do
  assertTextContains "CLI help documents exception checks" LeanFmt.Cli.usage
    "--check-exception"
  assertTextContains "CLI help documents environment cache control"
    LeanFmt.Cli.usage "--env-cache-size"
  assertTextContains "CLI help documents import-first environment control"
    LeanFmt.Cli.usage "--import-env-first"
  assertTextContains "CLI help documents hidden-path override"
    LeanFmt.Cli.usage "--include-hidden"
  assertTextLacks "CLI help omits replaced preservation option"
    LeanFmt.Cli.usage "--check-preserves-code"
  assertTextLacks "CLI help omits replaced unknown-rule option"
    LeanFmt.Cli.usage "--report-unknown-rules"
  match LeanFmt.Cli.parseArgs ["--check", "GraphQL.lean", "LeanFmt.lean"] with
  | .run options =>
      assertTrue "CLI check flag" options.check
      assertTrue "CLI file order"
        (options.files.map toString == ["GraphQL.lean", "LeanFmt.lean"])
  | result =>
      throw
      <| IO.userError s!"CLI parser should accept --check and files: {repr result}"
  match LeanFmt.Cli.parseArgs ["--check-exception", "GraphQL.lean"] with
  | .run options =>
      assertTrue "CLI exception check flag" options.checkException
      assertTrue "CLI exception check does not imply no-write check" (!options.check)
      assertTrue "CLI exception check file order"
        (options.files.map toString == ["GraphQL.lean"])
  | result =>
      throw
      <| IO.userError
          s!"CLI parser should accept --check-exception and files: {repr result}"
  match LeanFmt.Cli.parseArgs ["--check-idempotent", "GraphQL.lean"] with
  | .run options =>
      assertTrue "CLI idempotence check flag" options.checkIdempotent
      assertTrue "CLI idempotence does not imply no-write check" (!options.check)
      assertTrue "CLI idempotence file order"
        (options.files.map toString == ["GraphQL.lean"])
  | result =>
      throw
      <| IO.userError
          s!"CLI parser should accept --check-idempotent and files: {repr result}"
  match LeanFmt.Cli.parseArgs
          ["--check", "--check-exception", "--check-idempotent", "GraphQL.lean"] with
  | .run options =>
      assertTrue "CLI combined check flag" options.check
      assertTrue "CLI combined exception flag" options.checkException
      assertTrue "CLI combined idempotence flag" options.checkIdempotent
  | result =>
      throw
      <| IO.userError s!"CLI parser should accept combined check flags: {repr result}"
  match LeanFmt.Cli.parseArgs ["--env-cache-size", "0", "GraphQL.lean"] with
  | .run options =>
      assertTrue "CLI environment cache size flag" (options.environmentCacheSize == 0)
  | result =>
      throw
      <| IO.userError
          s!"CLI parser should accept --env-cache-size and files: {repr result}"
  match LeanFmt.Cli.parseArgs ["--env-cache-size", "nope", "GraphQL.lean"] with
  | .error "invalid --env-cache-size value: nope" => pure ()
  | result =>
      throw
      <| IO.userError
          s!"CLI parser should reject invalid --env-cache-size: {repr result}"
  match LeanFmt.Cli.parseArgs ["--env-cache-size"] with
  | .error "--env-cache-size requires a value" => pure ()
  | result =>
      throw
      <| IO.userError
          s!"CLI parser should require --env-cache-size value: {repr result}"
  match LeanFmt.Cli.parseArgs ["--import-env-first", "GraphQL.lean"] with
  | .run options =>
      assertTrue "CLI import-first environment flag" options.importEnvironmentFirst
  | result =>
      throw
      <| IO.userError
          s!"CLI parser should accept --import-env-first and files: {repr result}"
  for testOnlyOption in ["--profile", "--update-fixture", "--trace-renderer"] do
    match LeanFmt.Cli.parseArgs [testOnlyOption, "GraphQL.lean"] with
    | .error message =>
        assertEq s!"public CLI rejects {testOnlyOption}"
          s!"unknown option: {testOnlyOption}" message
    | result =>
        throw
        <| IO.userError
            s!"public CLI should reject {testOnlyOption}, got: {repr result}"
  match Cli.parseArgs ["--profile", "GraphQL.lean"] with
  | .run options =>
      assertTrue "CLI profile flag" options.profile
      assertTrue "CLI profile does not imply no-write check" (!options.check)
  | result =>
      throw <| IO.userError s!"CLI parser should accept --profile: {repr result}"
  match LeanFmt.Cli.parseArgs ["--report-unknown-rules", "GraphQL.lean"] with
  | .error "unknown option: --report-unknown-rules" => pure ()
  | result =>
      throw
      <| IO.userError s!"CLI should reject replaced unknown-rule option: {repr result}"
  match LeanFmt.Cli.parseArgs ["--recursive", "GraphQL"] with
  | .run _ => pure ()
  | result =>
      throw <| IO.userError s!"CLI parser should accept --recursive: {repr result}"
  match LeanFmt.Cli.parseArgs ["-r", "GraphQL"] with
  | .run _ => pure ()
  | result =>
      throw <| IO.userError s!"CLI parser should accept -r: {repr result}"
  match LeanFmt.Cli.parseArgs ["--include-hidden", "GraphQL"] with
  | .run options =>
      assertTrue "CLI include-hidden flag" options.includeHidden
  | result =>
      throw <| IO.userError s!"CLI parser should accept --include-hidden: {repr result}"
  match Cli.parseArgs ["--update-fixture", "--trace-renderer", "fixture.leanfmt"] with
  | .run options =>
      assertTrue "CLI update fixture trace mode" (options.mode == .updateFixture)
      assertTrue "CLI renderer trace flag" options.traceRenderer
      assertTrue "CLI trace file order"
        (options.files.map toString == ["fixture.leanfmt"])
  | result =>
      throw
      <| IO.userError
          s!"CLI parser should accept --update-fixture --trace-renderer: {repr result}"
  match Cli.parseArgs ["--trace-renderer", "GraphQL.lean"] with
  | .error "--trace-renderer requires --update-fixture" => pure ()
  | result =>
      throw
      <| IO.userError
          s!"CLI parser should require --update-fixture for --trace-renderer: {repr result}"
  match LeanFmt.Cli.parseArgs [] with
  | .error "no input files" => pure ()
  | result =>
      throw <| IO.userError s!"CLI parser should require files: {repr result}"

def assertEnvironmentCacheBound (env : Lean.Environment) : IO Unit := do
  let keys (entries : List (String × Lean.Environment))
      : String :=
    String.intercalate "," (entries.map Prod.fst)
  let entries ← IO.mkRef []
  let cache : LeanFmt.Cli.EnvironmentCache :=
    { default := env, maxEntries := 2, entries }
  cache.rememberEnvironment "first" env
  cache.rememberEnvironment "second" env
  cache.rememberEnvironment "third" env
  assertEq "environment cache evicts least-recently remembered entry"
    "third,second" (keys (← entries.get))
  cache.rememberEnvironment "second" env
  assertEq "environment cache refreshes remembered entry"
    "second,third" (keys (← entries.get))
  let disabledEntries ← IO.mkRef []
  let disabledCache : LeanFmt.Cli.EnvironmentCache :=
    { default := env, maxEntries := 0, entries := disabledEntries }
  disabledCache.rememberEnvironment "ignored" env
  assertTrue "disabled environment cache remains empty" (← disabledEntries.get).isEmpty

def assertFormattingExceptionChecks (env : Lean.Environment) : IO Unit := do
  assertTrue "whitespace-only edits preserve code"
    (← codePreservedIgnoringWhitespace env "def x : Nat := 0\n" "def   x:Nat:=0\n")
  assertTrue "token edits do not preserve code"
    (!(← codePreservedIgnoringWhitespace env "def x : Nat := 0\n" "def y : Nat := 0\n"))
  assertTrue "whitespace cannot move an identifier boundary"
    (!(← codePreservedIgnoringWhitespace env
          "def value := ab c\n" "def value := a bc\n"))
  assertTrue "whitespace outside comments is normalized"
    (← codePreservedIgnoringWhitespace env
        "def value:=0-- keep  spaces\n"
        "def value := 0 -- keep  spaces\n")
  assertTrue "line-comment whitespace is preserved"
    (!(← codePreservedIgnoringWhitespace env
          "def value := 0 -- keep  spaces\n"
          "def value := 0 -- keep spaces\n"))
  assertTrue "comments remain ordered relative to code"
    (!(← codePreservedIgnoringWhitespace env
          "def value := 0 -- keep comment\n"
          "-- keep comment\ndef value := 0\n"))
  assertTrue "layout-only empty syntax nodes are ignored"
    (← codePreservedIgnoringWhitespace env
        "def value := f <| { invFun := g }\n"
        "def value := f <| {\n  invFun := g\n}\n")
  assertTrue "module-doc whitespace is preserved" (!(← codePreservedIgnoringWhitespace env
          "namespace X\n/-! keep  spaces -/\nend X\n"
          "namespace X\n/-!\n  keep  spaces -/\nend X\n"))
  let declarationDocWhitespacePreserved ← codePreservedIgnoringWhitespace env
      "/-- keep  spaces -/\ndef value := 0\n"
      "/--\n  keep  spaces -/\ndef value := 0\n"
  assertTrue "declaration-doc whitespace is preserved"
    (!declarationDocWhitespacePreserved)
  let nestedBlockCommentWhitespacePreserved ← codePreservedIgnoringWhitespace env
      "def value := /- outer /- keep  spaces -/ comment -/ 0\n"
      "def value := /- outer /- keep spaces -/ comment -/ 0\n"
  assertTrue "nested block-comment whitespace is preserved"
    (!nestedBlockCommentWhitespacePreserved)
  assertTrue "string-literal whitespace remains code"
    (!(← codePreservedIgnoringWhitespace env
          "def value := \"keep  spaces\"\n"
          "def value := \"keep spaces\"\n"))
  let longIdentifier := String.ofList (List.replicate (Formatter.maxLineWidth + 1) 'x')
  let overflow := s!"def overflow := {longIdentifier} y\n"
  let overflowModule ←
    SyntaxTree.parseModuleStringWithEnv env overflow "overflow-diagnostic.lean"
  match Formatter.Diagnostics.overflowOccurrences overflowModule with
  | [occurrence] =>
      assertTrue "overflow occurrence line" (occurrence.line == 1)
      assertTrue "overflow occurrence width" (Formatter.maxLineWidth < occurrence.width)
  | occurrences =>
      throw <| IO.userError s!"expected one overflow occurrence, got {repr occurrences}"
  let singleTokenOverflow := s!"def overflow := {longIdentifier}\n"
  let singleTokenModule ←
    SyntaxTree.parseModuleStringWithEnv env singleTokenOverflow
      "single-token-overflow.lean"
  assertTrue "single-token overflow is exempt"
    (Formatter.Diagnostics.overflowOccurrences singleTokenModule).isEmpty
  let atomicCloseOverflow := s!"def overflow := ({longIdentifier})\n"
  let atomicCloseModule ←
    SyntaxTree.parseModuleStringWithEnv env atomicCloseOverflow
      "atomic-close-overflow.lean"
  assertTrue "atomic token and closing delimiter overflow is exempt"
    (Formatter.Diagnostics.overflowOccurrences atomicCloseModule).isEmpty
  let atomicCloseCommaOverflow := s!"def values := [\n  ({longIdentifier}),\n]\n"
  let atomicCloseCommaModule ←
    SyntaxTree.parseModuleStringWithEnv env atomicCloseCommaOverflow
      "atomic-close-comma-overflow.lean"
  assertTrue "atomic token, closing delimiter, and comma overflow is exempt"
    (Formatter.Diagnostics.overflowOccurrences atomicCloseCommaModule).isEmpty
  let lineCommentOverflow :=
    "def comment := 0 -- "
    ++ String.ofList (List.replicate Formatter.maxLineWidth 'x')
    ++ "\n"
  let lineCommentModule ←
    SyntaxTree.parseModuleStringWithEnv env lineCommentOverflow
      "line-comment-overflow.lean"
  assertTrue "line-comment overflow is exempt"
    (Formatter.Diagnostics.overflowOccurrences lineCommentModule).isEmpty
  let blockCommentOverflow :=
    "/- " ++ String.ofList (List.replicate Formatter.maxLineWidth 'x') ++ " -/\n"
  let blockCommentModule ←
    SyntaxTree.parseModuleStringWithEnv env blockCommentOverflow
      "block-comment-overflow.lean"
  assertTrue "block-comment overflow is exempt"
    (Formatter.Diagnostics.overflowOccurrences blockCommentModule).isEmpty
  let proofOverflow :=
    "theorem preservedProofOverflow : True := by\n"
    ++ "  have veryLongProofName := "
    ++ String.ofList (List.replicate Formatter.maxLineWidth 'x')
    ++ "\n"
    ++ "  exact True.intro\n"
  let proofOverflowModule ←
    SyntaxTree.parseModuleStringWithEnv env proofOverflow "proof-overflow.lean"
  assertTrue "preserved proof overflow is exempt"
    (Formatter.Diagnostics.overflowOccurrences proofOverflowModule).isEmpty
  let interpolatedStringOverflow :=
    "def message := s!\""
    ++ String.ofList (List.replicate Formatter.maxLineWidth 'x')
    ++ "{value}\"\n"
  let interpolatedStringModule ←
    SyntaxTree.parseModuleStringWithEnv env interpolatedStringOverflow
      "interpolated-string-overflow.lean"
  assertTrue "interpolated-string tree overflow is exempt"
    (Formatter.Diagnostics.overflowOccurrences interpolatedStringModule).isEmpty
  let stringCommaOverflow :=
    "def messages := [\n  \""
    ++ String.ofList (List.replicate Formatter.maxLineWidth 'x')
    ++ "\",\n  \"short\",\n]\n"
  let stringCommaModule ←
    SyntaxTree.parseModuleStringWithEnv env stringCommaOverflow
      "string-comma-overflow.lean"
  assertTrue "string and trailing comma tree overflow is exempt"
    (Formatter.Diagnostics.overflowOccurrences stringCommaModule).isEmpty
  let atomicCommaOverflow :=
    "def values := [\n  " ++ longIdentifier ++ ",\n  short,\n]\n"
  let atomicCommaModule ←
    SyntaxTree.parseModuleStringWithEnv env atomicCommaOverflow
      "atomic-comma-overflow.lean"
  assertTrue "atomic tree and trailing comma overflow is exempt"
    (Formatter.Diagnostics.overflowOccurrences atomicCommaModule).isEmpty
  let counts : LeanFmt.Cli.ExceptionCounts :=
    {
      codeChanged := 1,
      lineOverflow := 2,
      missingRule := 3,
      missingRuleWithRegisteredLeanFormatter := 1,
      missingRuleWithParserDescription := 1,
      missingRuleWithoutLeanFormatter := 1,
      formatFallback := 4,
      notIdempotent := 5
    }
  assertEq "CLI exception summary includes every kind"
    (String.intercalate "\n"
      [
        "exception counts:",
        "  code changed: 1",
        "  line overflow: 2",
        "  missing rule: 3",
        "    registered Lean formatter: 1",
        "    Lean parser description: 1",
        "    no Lean formatter metadata: 1",
        "  format fallback: 4",
        "  not idempotent: 5"
      ])
    counts.summary

def assertCliChecksStillFormatUnlessCheck (env : Lean.Environment) : IO Unit := do
  let root : FilePath := ".lake/leanfmt-cli-test/checks"
  IO.FS.createDirAll root
  let preservingFile := root / "Preserving.lean"
  let preservingSource := "def  preserving  : Nat := 0\n"
  IO.FS.writeFile preservingFile preservingSource
  let preservingExitCode ←
    LeanFmt.Cli.runOptions
      { checkException := true, includeHidden := true, files := [preservingFile] }
  assertTrue "CLI exception check still formats" (preservingExitCode == 0)
  let preservingFormatted ←
    Formatter.formatSourceWithEnv env preservingSource preservingFile.toString
  assertEq "CLI exception check writes formatted output"
    preservingFormatted (← IO.FS.readFile preservingFile)

  let overflowFile := root / "Overflow.lean"
  let overflowSource :=
    "def "
    ++ String.ofList (List.replicate (Formatter.maxLineWidth + 1) 'x')
    ++ " := 0\n"
  IO.FS.writeFile overflowFile overflowSource
  let afterExceptionFile := root / "AfterException.lean"
  let afterExceptionSource := "def  afterException  : Nat := 0\n"
  IO.FS.writeFile afterExceptionFile afterExceptionSource
  let overflowExitCode ←
    LeanFmt.Cli.runOptions
      {
        checkException := true
        includeHidden := true
        files := [overflowFile, afterExceptionFile]
      }
  assertTrue "CLI exception check rejects remaining overflow" (overflowExitCode == 1)
  assertEq "CLI exception failure prevents writes"
    overflowSource (← IO.FS.readFile overflowFile)
  let afterExceptionFormatted ←
    Formatter.formatSourceWithEnv env afterExceptionSource afterExceptionFile.toString
  assertEq "CLI continues with files after an exception"
    afterExceptionFormatted (← IO.FS.readFile afterExceptionFile)

  let idempotentFile := root / "Idempotent.lean"
  let idempotentSource := "def  idempotent  : Nat := 0\n"
  IO.FS.writeFile idempotentFile idempotentSource
  let idempotentExitCode ←
    LeanFmt.Cli.runOptions
      { checkIdempotent := true, includeHidden := true, files := [idempotentFile] }
  assertTrue "CLI idempotence check still formats" (idempotentExitCode == 0)
  let idempotentFormatted ←
    Formatter.formatSourceWithEnv env idempotentSource idempotentFile.toString
  assertEq "CLI idempotence check writes formatted output"
    idempotentFormatted (← IO.FS.readFile idempotentFile)

  let checkedFile := root / "Checked.lean"
  let checkedSource := "def  checked  : Nat := 0\n"
  IO.FS.writeFile checkedFile checkedSource
  let checkedExitCode ←
    LeanFmt.Cli.runOptions
      {
        check := true
        checkException := true
        checkIdempotent := true
        includeHidden := true
        files := [checkedFile]
      }
  assertTrue "CLI diagnostic --check ignores formatting changes" (checkedExitCode == 0)
  assertEq "CLI diagnostic --check remains a dry run"
    checkedSource (← IO.FS.readFile checkedFile)

  let ordinaryCheckExitCode ←
    LeanFmt.Cli.runOptions
      { check := true, includeHidden := true, files := [checkedFile] }
  assertTrue "CLI ordinary --check still fails on formatting changes"
    (ordinaryCheckExitCode == 1)

def assertCliFormatsDirectory (env : Lean.Environment) : IO Unit := do
  let root : FilePath := ".lake/leanfmt-cli-test/nonrecursive"
  let nested : FilePath := root / "nested"
  IO.FS.createDirAll nested
  let topFile := root / "Top.lean"
  let nestedFile := nested / "Nested.lean"
  let topSource := "def  top  : Nat := 0\n"
  let nestedSource := "def  nested  : Nat := 0\n"
  IO.FS.writeFile topFile topSource
  IO.FS.writeFile nestedFile nestedSource
  let exitCode ← LeanFmt.Cli.runOptions { includeHidden := true, files := [root] }
  assertTrue "CLI directory format succeeds" (exitCode == 0)
  let topFormatted ← Formatter.formatSourceWithEnv env topSource topFile.toString
  assertEq "CLI formats direct Lean files in directory" topFormatted
    (← IO.FS.readFile topFile)
  assertEq "CLI non-recursive directory formatting skips nested Lean files"
    nestedSource (← IO.FS.readFile nestedFile)

def assertCliFormatsDirectoryRecursively (env : Lean.Environment) : IO Unit := do
  let root : FilePath := ".lake/leanfmt-cli-test/recursive"
  let nested : FilePath := root / "nested"
  IO.FS.createDirAll nested
  let topFile := root / "Top.lean"
  let nestedFile := nested / "Nested.lean"
  let topSource := "def  top  : Nat := 0\n"
  let nestedSource := "def  nested  : Nat := 0\n"
  IO.FS.writeFile topFile topSource
  IO.FS.writeFile nestedFile nestedSource
  match LeanFmt.Cli.parseArgs ["-r", "--include-hidden", root.toString] with
  | .run options =>
      let exitCode ← LeanFmt.Cli.runOptions options
      assertTrue "CLI recursive directory format succeeds" (exitCode == 0)
      let topFormatted ← Formatter.formatSourceWithEnv env topSource topFile.toString
      let nestedFormatted ←
        Formatter.formatSourceWithEnv env nestedSource nestedFile.toString
      assertEq "CLI recursive directory formatting formats direct Lean files"
        topFormatted (← IO.FS.readFile topFile)
      assertEq "CLI recursive directory formatting formats nested Lean files"
        nestedFormatted (← IO.FS.readFile nestedFile)
  | result =>
      throw
      <| IO.userError s!"CLI parser should accept recursive directory: {repr result}"

def assertCliSkipsHiddenPathsByDefault : IO Unit :=
  IO.FS.withTempDir
    fun root =>
      do
        let visibleFile := root / "Visible.lean"
        let hiddenFile := root / ".Hidden.lean"
        let visibleDir := root / "visible"
        let hiddenDir := root / ".hidden"
        let visibleNestedFile := visibleDir / "Nested.lean"
        let hiddenNestedFile := hiddenDir / "Nested.lean"
        IO.FS.createDirAll visibleDir
        IO.FS.createDirAll hiddenDir
        for file in [visibleFile, hiddenFile, visibleNestedFile, hiddenNestedFile] do
          IO.FS.writeFile file "def value : Nat := 0\n"

        let defaultFiles ←
          LeanFmt.Cli.expandInputPaths { recursive := true, files := [root] }
        assertTrue "CLI discovers visible direct files"
          (defaultFiles.contains visibleFile)
        assertTrue "CLI discovers visible nested files"
          (defaultFiles.contains visibleNestedFile)
        assertTrue "CLI skips hidden files" (!defaultFiles.contains hiddenFile)
        assertTrue "CLI skips hidden directories"
          (!defaultFiles.contains hiddenNestedFile)

        let explicitHiddenFile ←
          LeanFmt.Cli.expandInputPaths { files := [hiddenNestedFile] }
        assertTrue "CLI processes an explicitly supplied file under a hidden directory"
          (explicitHiddenFile == [hiddenNestedFile])

        let hiddenChildFile := hiddenDir / ".Child.lean"
        IO.FS.writeFile hiddenChildFile "def child : Nat := 0\n"
        let explicitHiddenDirectory ←
          LeanFmt.Cli.expandInputPaths { recursive := true, files := [hiddenDir] }
        assertTrue "CLI enters an explicitly supplied hidden directory"
          (explicitHiddenDirectory.contains hiddenNestedFile)
        assertTrue "CLI still skips hidden entries inside an explicit hidden directory"
          (!explicitHiddenDirectory.contains hiddenChildFile)

        let includedFiles ←
          LeanFmt.Cli.expandInputPaths
            { recursive := true, includeHidden := true, files := [root] }
        for file
            in [
              visibleFile,
              hiddenFile,
              visibleNestedFile,
              hiddenNestedFile,
              hiddenChildFile
            ] do
          assertTrue s!"CLI --include-hidden discovers {file}"
            (includedFiles.contains file)

def assertCliLoadsImportedSyntax : IO Unit := do
  let root : FilePath := ".lake/leanfmt-cli-test/project-env"
  IO.FS.createDirAll root
  let file := root / "ImportedSyntax.lean"
  let source := "import LeanFmt.Tests.ProjectSyntax\n\n#check project_syntax\n"
  IO.FS.writeFile file source
  let exitCode ← LeanFmt.Cli.runOptions { includeHidden := true, files := [file] }
  assertTrue "CLI loads syntax from imported modules" (exitCode == 0)
  assertEq "CLI preserves imported syntax source" source (← IO.FS.readFile file)

def assertFmtExecutableConfigured : IO Unit := do
  let lakefile ← IO.FS.readFile "lakefile.toml"
  assertTextContains "lakefile uses namespaced test driver" lakefile
    "testDriver = \"LeanFmt.Tests\""
  assertTextContains "lakefile defines namespaced test library" lakefile
    "name = \"LeanFmt.Tests\""
  assertTextContains "test library uses suite root" lakefile
    "roots = [\"LeanFmt.Tests.Suite\"]"
  assertTextContains "lakefile defines fmt executable" lakefile "name = \"fmt\""
  assertTextContains "fmt executable uses LeanFmt.Cli root" lakefile
    "root = \"LeanFmt.Cli\""
  assertTextContains "lakefile defines test CLI" lakefile "name = \"fmt-test\""
  assertTextContains "test CLI uses LeanFmt.Tests.Main root" lakefile
    "root = \"LeanFmt.Tests.Main\""

def assertRendererTraceIncludesPathAndState (env : Lean.Environment) : IO Unit := do
  let source :=
    "def traceExample : Result := veryLongFunctionNameForTreeFormatting firstArgumentNameForTree secondArgumentNameForTree\n"
  let moduleTree ← SyntaxTree.parseModuleStringWithEnv env source "trace-example.lean"
  let (_formatted, trace) := Formatter.Debug.formatModuleWithTrace moduleTree
  assertTextContains "renderer trace includes formatted line"
    trace "line 1 | def traceExample : Result :="
  assertTextContains "renderer trace interleaves trace under formatted line"
    trace "line 1 | def traceExample : Result :=\n  path="
  assertTextContains "renderer trace includes segment path" trace "path="
  assertTextContains "renderer trace includes segment range" trace "segment=["
  assertTextContains "renderer trace includes node kind" trace "kind="
  assertTextContains "renderer trace includes selected rule" trace "rule="
  assertTextContains "renderer trace includes current column" trace "currentColumn="
  assertTextContains "renderer trace includes segment indentation" trace
    "segmentIndentation="
  assertTextContains "renderer trace includes tail indentation" trace "tailIndentation="

def assertCliFixtureUpdate (env : Lean.Environment) : IO Unit := do
  let separator :=
    Cli.fixtureSeparatorRule
    ++ "\n"
    ++ "-- leanfmt: expected output below (DO NOT EDIT)\n"
    ++ Cli.fixtureSeparatorRule
  let source := "def  f  (x  : Nat)  := x\n"
  let staleExpected := "def stale := 0\n"
  let original := source ++ separator ++ "\n" ++ staleExpected
  let expectedFormatted ← Formatter.formatSourceWithEnv env source "fixture-source.lean"
  let updated ← Cli.updateFixtureContent env "fixture.leanfmt" original
  let expected := source ++ separator ++ "\n" ++ expectedFormatted
  assertEq "fixture update" expected updated

def assertFormatterArchitecture : IO Unit := do
  let application := SyntaxTree.Tree.node .application #[]
  let segment := Formatter.LineBreakRules.Segment.ofTree application
  let context : Formatter.LineBreakRules.RuleContext := {}
  let rule := Formatter.LineBreakRules.formattingRuleFor application
  assertTrue "application dispatch selects a flow rule" (rule.flow context segment)
  assertTrue "application rule is renderer-independent"
    (!(rule.breakPoints context segment).any
        fun breakPoint => breakPoint.index > segment.stop)
  let left := SyntaxTree.tokenOfNone .ident Lean.identKind "left"
  let right := SyntaxTree.tokenOfNone .ident Lean.identKind "right"
  assertEq "space rules own ordinary token spacing" " "
    (Formatter.SpaceRules.spaceBetweenTokens left right)
  let trace : Formatter.Trace.State := {}
  assertTrue "trace state starts disabled" (!trace.enabled)
  assertEq "internal normalization is shared" "a\nb\n"
    (Formatter.Internal.normalizeSource "a\r\nb\r")

def assertDeclarationRuleTransparent : IO Unit := do
  let tree :=
    SyntaxTree.Tree.node (SyntaxTree.NodeKind.raw `Lean.Parser.Command.declaration) #[]
  let segment := Formatter.LineBreakRules.Segment.ofTree tree
  let rule ←
    match Formatter.LineBreakRules.ruleFor tree with
    | some rule => pure rule
    | none => throw <| IO.userError "declaration rule missing"
  let context : Formatter.LineBreakRules.RuleContext := {}
  assertTrue "declaration rule has no source-break policy"
    (!rule.useExistingBreaks context segment)
  assertTrue "declaration rule is not mandatory" (!rule.mandatory context segment)
  assertTrue "declaration rule is not flow" (!rule.flow context segment)
  assertTrue "declaration rule has no break points"
    (rule.breakPoints context segment == [])

def assertMathlibLowRiskSyntaxKindsHaveRules : IO Unit := do
  let kinds : List Lean.SyntaxNodeKind :=
    [
      `Lean.Parser.Command.attribute,
      `Lean.Parser.Module.all,
      `Lean.Parser.Command.deprecated_module,
      `Lean.Parser.Command.assertNotImported,
      `Lean.Parser.Command.assertNotExists,
      `Lean.Parser.Command.namedPrio,
      `Lean.Parser.Command.openOnly,
      `Lean.Parser.Command.abbrev,
      `Lean.Parser.Command.classAbbrev,
      `Lean.Parser.Command.nonrec,
      `Lean.Parser.Command.notation,
      `Lean.Parser.Command.mixfix,
      `Lean.Parser.Command.macro,
      `Lean.Parser.Command.namedName,
      `Lean.Parser.Command.macroArg,
      `Lean.Parser.Command.macroTail,
      `Lean.Parser.Command.macroRhs,
      `Lean.Parser.Command.infix,
      `Lean.Parser.Command.infixl,
      `Lean.Parser.Command.infixr,
      `Lean.Parser.Command.prefix,
      `Lean.Parser.Command.postfix,
      `Lean.Parser.Command.identPrec,
      `Lean.Parser.Command.grindPattern,
      `Lean.Parser.Command.omit,
      `Lean.Parser.Command.include,
      `Lean.Parser.Command.structParent,
      `Lean.Parser.Command.structCtor,
      `Lean.Parser.Command.structInstBinder,
      `Lean.Parser.Command.structImplicitBinder,
      `Lean.Parser.Command.structExplicitBinder,
      `Lean.Parser.Command.extends,
      `Lean.Parser.Command.initialize_simps_projections,
      `Lean.Parser.Command.simpsProj,
      `Lean.Parser.Command.simpsRule,
      `Lean.Parser.Command.simpsRule.add,
      `Lean.Parser.Command.simpsRule.prefix,
      `Lean.Parser.Command.simpsRule.erase,
      `Lean.Parser.Command.eraseAttr,
      `Lean.Parser.Command.deriving,
      `Lean.Parser.Command.classInductive,
      `lemma,
      `Lean.Parser.Term.explicit,
      `Lean.Parser.Term.explicitUniv,
      `Lean.Parser.Term.have,
      `Lean.Parser.Term.haveI,
      `Lean.Parser.Term.suffices,
      `Lean.Parser.Term.sufficesDecl,
      `Lean.Parser.Term.open,
      `Lean.Parser.Term.termReturn,
      `Lean.Parser.Term.dynamicQuot,
      `Lean.Parser.Term.structInstFieldEqns,
      `Lean.Parser.Term.sort,
      `Lean.Parser.Term.letI,
      `Lean.Parser.Term.doLetExpr,
      `Lean.Parser.Term.doIfLetBind,
      `Lean.Parser.Term.doHave,
      `Lean.Parser.Term.inferInstanceAs,
      `Lean.Parser.Term.configItem,
      `Lean.Parser.Term.negConfigItem,
      `Lean.Parser.Term.doMatchExpr,
      `Lean.Parser.Term.matchExprAlts,
      `Lean.Parser.Term.matchExprAlt,
      `Lean.Parser.Term.matchExprElseAlt,
      `Lean.Parser.Term.matchExprPat,
      `Lean.Parser.Term.strictImplicitBinder,
      `Lean.Parser.Term.nofun,
      `Lean.Parser.Term.doNested,
      `Lean.Parser.Term.doSeqBracketed,
      `Lean.Parser.Tactic.tacticSeq,
      `Lean.Parser.Tactic.tacticSeq1Indented,
      `Lean.Parser.Tactic.exact,
      `Lean.Parser.Tactic.tacticRfl,
      `Lean.Parser.Tactic.grind,
      `Lean.Parser.Tactic.optConfig,
      `Lean.bracketedExplicitBinders,
      `scientific,
      `termℕ,
      `termℤ,
      `termℚ,
      `termℝ,
      `Nat.term_!,
      `coeNotation,
      `coeSortNotation,
      `coeFunNotation,
      `Lean.calc,
      `Lean.calcSteps,
      `Lean.calcFirstStep,
      `Lean.modCast,
      `Lean.«binderPred∈_»,
      `Lean.«binderPred<_»,
      `Lean.«binderPred>_»,
      `Lean.«binderPred≤_»,
      `Lean.«binderPred≥_»,
      `Lean.«binderPred≠_»,
      `Lean.«binderPred∉_»,
      `Mathlib.Meta.SetNotationForOrder.«binderPred⊆_»,
      `termDepIfThenElse,
      `boolIfThenElse,
      `BigOperators.bigsum,
      `BigOperators.bigprod,
      `BigOperators.bigOpBinders,
      `BigOperators.bigOpBinder,
      `Batteries.ExtendedBinder.extBinders,
      `Batteries.ExtendedBinder.extBinder,
      `Batteries.ExtendedBinder.extBinderCollection,
      `Batteries.ExtendedBinder.extBinderParenthesized,
      `Batteries.Tactic.Alias.alias,
      `Batteries.Tactic.Alias.aliasLR,
      `Batteries.Tactic.Lint.nolint,
      `Batteries.Util.LibraryNote.commandLibrary_note___,
      `Lean.Parser.Attr.simple,
      `Lean.Parser.Attr.simps,
      `Lean.Parser.Attr.attrSimps!_,
      `Lean.Parser.Attr.simpsArgsRest,
      `Lean.Parser.Attr.simpsConfig,
      `Lean.Parser.Attr.simpsConfigItem,
      `Lean.Parser.Attr.norm_cast,
      `Lean.Parser.Attr.ext,
      `Lean.Parser.Attr.higherOrder,
      `Lean.Parser.Attr.grindFwd,
      `Lean.Parser.Attr.grindBwd,
      `Lean.Parser.Attr.grindEqBoth,
      `Lean.Attr.coe,
      `Lean.Parser.Attr.instance,
      `Lean.deprecated,
      `token.existing,
      `Parser.Attr.functor_norm,
      `Parser.Attr.parity_simps,
      `Parser.Attr.fin_omega,
      `Parser.Attr.nontriviality,
      `Mathlib.Tactic.ToAdditive.to_additive,
      `Mathlib.Tactic.MkIff.mkIff,
      `Mathlib.Tactic.Translate.attrArgs,
      `Mathlib.Tactic.Translate.bracketedOption,
      `Mathlib.Tactic.Translate.translationHint,
      `Mathlib.Tactic.scopedNS,
      `Mathlib.Tactic.Push.pushAttr,
      `Mathlib.Tactic.GCongr.gcongrAttr,
      `Mathlib.Tactic.Monotonicity.Attr.mono,
      `Mathlib.Tactic.TermCongr.termCongr,
      `Mathlib.Elab.FastInstance.fastInstance,
      `Mathlib.Util.«commandCompile_inductive%_»,
      `Mathlib.Util.TermReduce.deltaStx,
      `Mathlib.Meta.setBuilder,
      `Mathlib.Meta.macroPattSetBuilder,
      `Mathlib.Meta.SetNotationForOrder.«binderPred⊂_»,
      `Mathlib.Notation3.notation3,
      `Mathlib.Notation3.notation3Item,
      `Mathlib.Notation3.identOptScoped,
      `LinearAlgebra.Projectivization.termℙ,
      `Qq.matcher,
      `Qq.doElemAssertInstancesCommute,
      `term.pseudo.antiquot,
      `Lean.termThrowError__,
      `Lean.Parser.«command__Dsimproc__[_]_(_):=_»,
      `Mathlib.CrossRef.wikidataTag,
      `Finsupp.Internal.stxSingle₀,
      `Finsupp.Internal.stxUpdate₀,
      `Aesop.Frontend.Parser.aesop,
      `Aesop.Frontend.Parser.aesopTactic,
      `Aesop.Frontend.Parser.bool_litTrue,
      `Aesop.Frontend.Parser.declareRuleSets,
      `Aesop.Frontend.Parser.attr_rules_,
      `Aesop.Frontend.Parser.rule_expr_,
      `Aesop.Frontend.Parser.rule_expr___,
      `Aesop.Frontend.Parser.ruleSetsFeature,
      `Aesop.Frontend.Parser.feature_,
      `Aesop.Frontend.Parser.feature__1,
      `Aesop.Frontend.Parser.feature__2,
      `Aesop.Frontend.Parser.feature__4,
      `Aesop.Frontend.Parser.phaseSafe,
      `Aesop.Frontend.Parser.phaseNorm,
      `Aesop.Frontend.Parser.phaseUnsafe,
      `Aesop.Frontend.Parser.builder_nameApply,
      `Aesop.Frontend.Parser.«priority_%»,
      `Aesop.Frontend.Parser.«priority-_»,
      `Lean.Parser.Level.hole,
      `Lean.Parser.Level.paren,
      `Lean.Parser.Level.max,
      `Lean.Parser.Tactic.quot,
      `PiNotation.piNotation,
      `prioLow,
      `prioHigh,
      `Lean.Parser.precedence,
      `precMax,
      `cfcTac,
      `adaptationNoteCmd,
      `wikidataId,
      `goldenRatio.termφ,
      `goldenRatio.termψ,
      `Topology.term𝓝,
      `FinsetFamily.term𝓒,
      `FinsetFamily.term𝓓,
      `Cardinal.termℵ₀,
      `Matroid.aesop_mat,
      `Matroid.ExchangeProperty.aesop_mat,
      `aesop_graph,
      `CategoryTheory.cat_disch,
      `proof_wanted,
      `BigOperators.bigexpect,
      `Std.termF!_,
      `antiquotNestedExpr,
      `precArg,
      `Matrix.vecNotation
    ]
  for kind in kinds do
    let tree := SyntaxTree.Tree.node (.raw kind) #[]
    assertTrue s!"mathlib low-risk syntax has rule: {kind}"
      (Formatter.LineBreakRules.ruleFor tree).isSome
  let vectorItems :=
    SyntaxTree.Tree.node (.raw `null)
      #[
        .leaf (syntheticAtomToken "a"),
        .leaf (syntheticAtomToken ","),
        .leaf (syntheticAtomToken "b")
      ]
  let vectorTree :=
    SyntaxTree.Tree.node (.raw `Matrix.vecNotation)
      #[.leaf (syntheticAtomToken "!["), vectorItems, .leaf (syntheticAtomToken "]")]
  match Formatter.LineBreakRules.ruleFor vectorTree with
  | some rule =>
      assertEq "matrix vector notation uses array rule" "array" rule.name
      let vectorSegment := Formatter.LineBreakRules.Segment.ofTree vectorTree
      assertTrue "matrix vector notation has item and close breaks"
        (rule.breakPoints {} vectorSegment
          == [{ index := 1, indentLevels := 1 }, { index := 2, indentLevels := 0 }])
      let itemSegment := Formatter.LineBreakRules.Segment.ofTree vectorItems
      let itemContext :=
        ({} : Formatter.LineBreakRules.RuleContext).push vectorSegment 1
      assertTrue "matrix vector notation item wrapper uses array item breaks"
        (Formatter.LineBreakRules.arrayItemBreaks itemContext itemSegment
          == [{ index := 2, indentLevels := 0 }])
  | none => throw <| IO.userError "matrix vector notation has no rule"
  let ignoredKindNames :=
    [
      "token.«←»",
      "_private.0.SzemerediRegularity.termM",
      "termℂ",
      "ComplexConjugate.termConj",
      "Bundle.termπ__",
      "«term⅟_»",
      "Set.«term⋃_,_»",
      "Batteries.ExtendedBinder.«term∀ᵉ_,_»",
      "«stx_*»",
      "Lean.Parser.Command.«stx_,*»",
      "Lean.Elab.Command.command_Irreducible_def____"
    ]
  for kindName in ignoredKindNames do
    assertTrue s!"custom syntax kind is ignored by missing-rule report: {kindName}"
      (Formatter.Diagnostics.missingRuleReportIgnoresKindName kindName)
  assertTrue "non-term custom syntax kind still needs an explicit rule"
    (!Formatter.Diagnostics.missingRuleReportIgnoresKindName
        "Aesop.Frontend.Parser.aesop")
  assertTrue "non-term guillemet syntax kind still needs an explicit rule"
    (!Formatter.Diagnostics.missingRuleReportIgnoresKindName "«tacticFoo»")
  let tacticTree := SyntaxTree.Tree.node (.raw `Mathlib.Tactic.ToDual.to_dual) #[]
  assertTrue "mathlib tactic syntax keeps original formatting"
    (Formatter.shouldEmitOriginalTree tacticTree)
  assertTrue "mathlib tactic syntax is skipped by missing-rule reporting"
    (Formatter.Diagnostics.missingRuleOccurrences "" none tacticTree).isEmpty
  let qqTermTree := SyntaxTree.Tree.node (.raw `Qq.«termQ(__)») #[]
  assertTrue "Qq term quotation keeps original formatting"
    (Formatter.shouldEmitOriginalTree qqTermTree)
  let qqEqTree := SyntaxTree.Tree.node (.infixChain `Qq.«term_=Q_») #[]
  assertTrue "Qq infix quotation keeps original formatting"
    (Formatter.shouldEmitOriginalTree qqEqTree)
  let simprocTree :=
    SyntaxTree.Tree.node (.raw `Lean.Parser.«command_Simproc_decl_(_):=_») #[]
  assertTrue "simproc declarations keep original formatting"
    (Formatter.shouldEmitOriginalTree simprocTree)

def assertMissingRuleCheckUsesDispatch (env : Lean.Environment) : IO Unit := do
  let unknownTree :=
    SyntaxTree.Tree.node
      (SyntaxTree.NodeKind.raw `Lean.Parser.Term.syntheticUnknownForTest) #[]
  assertTrue "unknown raw node is reported"
    (!(Formatter.LineBreakRules.ruleFor unknownTree).isSome)
  let knownTree := SyntaxTree.Tree.node .application #[]
  assertTrue "known logical node has a rule"
    ((Formatter.LineBreakRules.ruleFor knownTree).isSome)
  let doLetElseTree := SyntaxTree.Tree.node (.raw `Lean.Parser.Term.doLetElse) #[]
  match Formatter.LineBreakRules.ruleFor doLetElseTree with
  | some rule => assertEq "do-let fallback rule name" "doLetElse" rule.name
  | none => throw <| IO.userError "do-let fallback wrapper has no rule"
  let source := "foo"
  let token :=
    SyntaxTree.tokenOfSynthetic .ident Lean.identKind "foo"
      (String.Pos.Raw.mk 0) (String.Pos.Raw.mk 3)
  let sourceTree :=
    SyntaxTree.Tree.node
      (SyntaxTree.NodeKind.raw `Lean.Parser.Term.syntheticUnknownForTest)
      #[.leaf token]
  let occurrences := Formatter.Diagnostics.missingRuleOccurrences source none sourceTree
  assertTrue "missing-rule occurrence includes source"
    (occurrences.any
      fun occurrence =>
        occurrence.kind == "Lean.Parser.Term.syntheticUnknownForTest"
        && occurrence.syntaxKind? == some `Lean.Parser.Term.syntheticUnknownForTest
        && occurrence.line == 1
        && occurrence.treeText == "foo")
  let customTokenTree :=
    SyntaxTree.Tree.node
      (SyntaxTree.NodeKind.raw `token.syntheticUnknownForTest)
      #[.leaf token]
  assertTrue "custom token syntax is ignored by missing-rule report"
    (Formatter.Diagnostics.missingRuleOccurrences source none customTokenTree).isEmpty
  let customTermTree :=
    SyntaxTree.Tree.node (SyntaxTree.NodeKind.raw `«term⅟_») #[.leaf token]
  assertTrue "custom term syntax is ignored by missing-rule report"
    (Formatter.Diagnostics.missingRuleOccurrences source none customTermTree).isEmpty
  let customNonTermTree :=
    SyntaxTree.Tree.node
      (SyntaxTree.NodeKind.raw `Aesop.Frontend.Parser.syntheticUnknownForTest)
      #[.leaf token]
  assertTrue "non-term custom syntax is reported"
    (!(Formatter.Diagnostics.missingRuleOccurrences source none
        customNonTermTree).isEmpty)
  let moduleTree : SyntaxTree.Module :=
    { source, rawSyntax := .missing, tree := sourceTree, tokens := sourceTree.tokens }
  let exceptions := Formatter.Diagnostics.formattingExceptions moduleTree moduleTree
  assertTrue "exception check includes missing rules"
    (exceptions.any
      fun exception =>
        match exception with
        | .missingRule occurrence =>
            occurrence.kind == "Lean.Parser.Term.syntheticUnknownForTest"
        | _ => false)
  assertTrue "registered Lean formatter is identified"
    (Formatter.Diagnostics.leanFormatterAvailability env (some `Lean.Parser.Term.app)
      == .registered)
  assertTrue "unknown syntax has no Lean formatter metadata"
    (Formatter.Diagnostics.leanFormatterAvailability env
        (some `Lean.Parser.Term.syntheticUnknownForTest)
      == .unavailable)
  let projectEnv ←
    SyntaxTree.importEnvironment #[{ module := `LeanFmt.Tests.ProjectSyntax }]
  assertTrue "parser description fallback is identified"
    (Formatter.Diagnostics.leanFormatterAvailability projectEnv (some `projectSyntax)
      == .parserDescription)

def assertSyntaxDeclarationsHaveRules (env : Lean.Environment) : IO Unit := do
  let source :=
    "syntax \"field \" str \"{\" term,* \"}\" : term\n"
    ++ "macro_rules\n"
    ++ "  | `(field $name:str { $selection,* }) => `(id)\n"
  let moduleTree ←
    SyntaxTree.parseModuleStringWithEnv env source "syntax-declaration-rules.lean"
  assertTrue "syntax declarations have complete rule coverage"
    (Formatter.Diagnostics.missingRuleOccurrencesForModule moduleTree).isEmpty
  let formatted ←
    Formatter.formatSourceWithEnv env source "syntax-declaration-rules.lean"
  assertTextContains "syntax separator stays tight" formatted "term,*"

def assertParserStateUpdatesAfterSyntaxCommands (env : Lean.Environment) : IO Unit := do
  let source :=
    "syntax \"customTerm\" : term\n"
    ++ "macro_rules\n"
    ++ "  | `(customTerm) => `(0)\n"
    ++ "macro \"finish_true\" : tactic => `(tactic| trivial)\n"
    ++ "def customAdd (left right : Nat) := left + right\n"
    ++ "infixl:65 \" ⊕ₜ \" => customAdd\n"
    ++ "postfix:max \"♯\" => Nat.succ\n"
    ++ "def syntaxValue := customTerm\n"
    ++ "def infixValue := 1 ⊕ₜ 2\n"
    ++ "def postfixValue := 1♯\n"
    ++ "example : True := by\n"
    ++ "  finish_true\n"
  let moduleTree ←
    SyntaxTree.parseModuleStringWithEnv env source "parser-state-syntax-commands.lean"
  assertTrue "syntax command parser-state updates preserve parseability"
    (!(moduleTree.tokens.isEmpty))

def assertCustomBracedTermSyntaxKeepsNestedSourceLayout (env : Lean.Environment)
    : IO Unit := do
  let source :=
    "syntax \"query \" \"{\" term,* \"}\" : term\n"
    ++ "syntax \"field \" str : term\n"
    ++ "syntax \"field \" str \" {\" term,* \"}\" : term\n"
    ++ "syntax \"on \" str \" {\" term,* \"}\" : term\n"
    ++ "\n"
    ++ "def abstractFieldOutputSnapshot : Operation :=\n"
    ++ "  query\n"
    ++ "    { field \"search\"\n"
    ++ "        { on \"Human\" { field \"id\", field \"homePlanet\" }, on \"Droid\" { field \"id\" } } }\n"
  let formatted ←
    Formatter.formatSourceWithEnv env source "custom-braced-term-source-layout.lean"
  assertEq "custom braced term syntax keeps nested source layout" source formatted

def assertPrefixedTermWrappersHaveRules (env : Lean.Environment) : IO Unit := do
  let source :=
    "def nestedAction : IO Nat := do\n"
    ++ "  pure (← pure 1)\n"
    ++ "\n"
    ++ "def initializer : IO Unit := do\n"
    ++ "  unsafe enableInitializersExecution\n"
  let moduleTree ←
    SyntaxTree.parseModuleStringWithEnv env source "prefixed-term-wrapper-rules.lean"
  assertTrue "prefixed term wrappers have complete rule coverage"
    (Formatter.Diagnostics.missingRuleOccurrencesForModule moduleTree).isEmpty
  let formatted ←
    Formatter.formatSourceWithEnv env source "prefixed-term-wrapper-rules.lean"
  assertEq "prefixed term wrappers stay attached" source formatted

def assertCslibStyleCoreSyntaxHasRules (env : Lean.Environment) : IO Unit := do
  let source :=
    "module\n"
    ++ "\n"
    ++ "public import Lean\n"
    ++ "\n"
    ++ "universe u\n"
    ++ "\n"
    ++ "public section\n"
    ++ "\n"
    ++ "namespace CslibLowRiskSyntax\n"
    ++ "\n"
    ++ "@[scoped grind =]\n"
    ++ "theorem scopedGrind (p : Prop) : p = p := by rfl\n"
    ++ "\n"
    ++ "open scoped Nat\n"
    ++ "\n"
    ++ "class HasWellFormed (α : Type u) where\n"
    ++ "  wf (x : α) : Prop\n"
    ++ "\n"
    ++ "example : True := by trivial\n"
    ++ "\n"
    ++ "end CslibLowRiskSyntax\n"
  let moduleTree ←
    SyntaxTree.parseModuleStringWithEnv env source "cslib-style-core-rules.lean"
  assertTrue "CSLib-style core syntax has complete rule coverage"
    (Formatter.Diagnostics.missingRuleOccurrencesForModule moduleTree).isEmpty

def runSyntaxTreeTests (env : Lean.Environment) : IO Unit := do
  assertSyntaxTreeRoundTrip env
  assertSyntaxTreeWhereRoundTrip env
  assertPreservationDetectsSyntaxChange env
  assertOverlappingQuotationTokensRemoved env
  assertTacticQuotationAntiquotationPreserved env
  assertOverlappingEmptySyntaxTokensRemoved env
  assertGroupedApplication env
  assertGroupedInfixChain env

def runBasicFormattingTests (env : Lean.Environment) : IO Unit := do
  assertSafeArrayIndexKeepsPostfixQuestion env
  assertPostfixSuperscriptSpacingPreservesParse env
  assertBlockCommentInternalWhitespacePreservedByFormatting env
  assertModuleDocInternalBlankLinesPreservedByFormatting env
  assertCustomNotationBracketSpacing
  assertOperatorLikeModifierTokenPreservesParse env
  assertSetOptionInBreaksAfterIn env
  assertCommandInWrapperPreservesBreakAfterIn env
  assertLeadingDotPatternConstructorsStayTight env
  assertFormatterConvergencePassLimit
  assertFormatterFallbackResultIsObservable env
  assertLayoutSensitiveTermsRemainParseableAndIdempotent env
  assertHardWhitespaceFormatting env
  assertImportsStayOnSeparateLines env
  assertLongImportStaysOnOneLine env
  assertNamespaceCommandsStayOnSeparateLines env
  assertCommentsDoNotBlockFormatting env
  assertLeadingCommentsPreserved env
  assertTrailingLineCommentPreserved env
  assertAnonymousConstructorAfterListKeepsSpace env
  assertAttributeDeclarationPreservesSourceBreak env
  assertAttributesFlowBeforeDeclarations env
  assertPrivateTheoremModifierStaysOnHeader env
  assertDoBlockPreservesBodyBreak env
  assertDoMatchAlternativesAlignWithMatch env
  assertDoBlockPreservesStatementBreaks env
  assertShowAndDoWrapperRules env
  assertProjectionChainDoesNotBreakBeforeDot env
  assertPipeProjectionKeepsTightDot env
  assertLongPipeProjectionKeepsTightDot env
  assertPipeProjectionInDeclarationTypeIndentsContinuation env
  assertPipeProjectionDoesNotBreakAfterDot env
  assertMatchAltProofRhsKeepsByOnArrowLine env
  assertRecordBraceSpacing env
  assertDerivingStaysOnOwnLine env
  assertStructureBreaksTopLevelFields env
  assertAbbrevSourceBreakAfterAssign env
  assertMatchArmKeepsDoOnArrowLine env
  assertWhereFormattingKeepsSuffix env
  assertProofBodyUntouched env
  assertShowProofTermUntouched env
  assertTheoremTermProofBodyUntouched env
  assertTheoremEquationProofBodyUntouched env
  assertDefinitionContainingProofUntouched env
  assertInstanceContainingProofUntouched env
  assertTerminationProofSuffixUntouched env
  assertBasicDeclarationBreak env
  assertDeclarationValueInfixBreaksAfterAssign env
  assertDeclarationValueKeepsAttachedByBody env
  assertDeclarationValueKeepsAttachedDoBody env
  assertProofValuesRemainLayoutIslands env
  assertCalcLayoutIslandAfterNestedInfix env
  assertHaveTermLayoutIsland env
  assertAbsoluteValueDelimitersStayAttached env
  assertSignatureParametersUseLeadingSourceBreakAfterFlatFails env
  assertDefinitionSourceBreakAfterAssignOverridesFlat env

def runExpressionAndRendererTests (env : Lean.Environment) : IO Unit := do
  assertSelfFormattingLetAndArrayRegressions env
  assertCliSelfFormattingRegressions env
  assertSelfFormattingRulePriorities env
  assertApplicationFlow env
  assertApplicationFitsBeforeSourceBreaks env
  assertNestedApplicationHonorsSourceBreaks env
  assertApplicationArgumentUsesHeadAnchorAfterTypeBreak env
  assertLetExpressionKeepsBodyBreak env
  assertLetIExpressionKeepsBodyBreak env
  assertLetExpressionBlocksFlatRendering env
  assertParenthesizedLetRhsIndentUnderImplication env
  assertLetBodyAfterInfixClosesLetLayout env
  assertDeclarationTypeBreak env
  assertImplicitBinderPreservesTightBraces env
  assertExplicitBinderTypeBreak env
  assertGroupedBinderIdentifiersFlow env
  assertSignatureParametersFitBeforeSourceBreaks env
  assertSignatureParametersStayOnHeaderWhenTheyFit env
  assertSignatureParameterSourceBreakFallback env
  assertVariableBinderSequenceFlows env
  assertMutualEquationArmIndent env
  assertMutualSingleLineParameterReturnIndent env
  assertReturnTypeInfixIndent env
  assertReturnTypeArrowFlows env
  assertLogicalArrowBreaksBalanced env
  assertChildFitCountsParentSuffix env
  assertColumnIndentationIsConservative
  assertSegmentBaseUsesRenderedStartColumn
  assertListApplicationColumnIndent env
  assertListApplicationSourceBreakIndent env
  assertSingletonArrayKeepsBodyBase env
  assertMultiItemArrayBreaksBalanced env
  assertOffColumnArrayRoundsOneLevel env
  assertInstanceWhereStaysWithHeader env
  assertInfixLeftDepth env
  assertInfixIgnoresFittingSourceBreaks env
  assertInfixIgnoresArbitrarySourceBreaks env
  assertInfixRhsFitsBeforeSourceBreaks env
  assertLogicalArrowSourceBreakIdempotent env
  assertApplicationSourceBreakInInfixLeftOperand env
  assertApplicationFlowBreakKeepsInfixDepthIdempotent env
  assertQuantifierBodyIgnoresParentInfixLeftDepth env
  assertParenthesizedQuantifierBlockIgnoresParentInfixLeftDepth env
  assertNestedInfixDoesNotDoubleCountOperatorWidth env
  assertNestedInfixKeepsHierarchy env
  assertApplicationInNestedInfixKeepsHierarchy env
  assertNestedLogicalApplicationLhsKeepsHierarchy env
  assertSubtypeBreaksBeforeProperty env
  assertAdjacentQuantifiersFitBeforeSourceBreaks env

def runControlFlowTests (env : Lean.Environment) : IO Unit := do
  assertIfThenElseRuleBreaksBalancedShape env
  assertShortIfThenElseStaysFlatInEquationArm env
  assertIfThenElseUsesExistingBreaks env
  assertElseIfContinuesOnElseLine env
  assertTermMatchAlternativesStayOnOwnLines env
  assertLetMatchAlternativesAlign env
  assertMatchArmPreservesSourceBreakBeforeShortRhs env
  assertIfThenElseBreaksBalanced env
  assertParenthesizedIfAlignsBeforeBranchIndent env
  assertMatchArmRhsIndent env
  assertMatchPeerBreakConsistency env
  assertMatchDiscriminantApplicationIndent env
  assertNestedTermMatchAlternativesAlign env
  assertNestedMatchAfterLambdaAlignsWithMatch env
  assertPrefixedMatchAlternativesAlignWithMatch env
  assertLambdaBodyUsesOperandAnchor env
  assertLambdaBinderSequenceBreaksBetweenBinders env
  assertQuantifierBreaksAfterComma env
  assertQuantifierIdentifierSequenceFlows env
  assertArrowQuantifierKeepsQuantifierOnArrowLine env
  assertArrowMatchKeepsMatchOnArrowLine env
  assertArrowMatchInMatchAltIdempotent env
  assertQuantifierBinderSequenceBreaksBetweenBinders env

def runCollectionAndDeclarationTests (env : Lean.Environment) : IO Unit := do
  assertInductiveConstructorIndentation env
  assertConstructorBinderContinuesFromUnbrokenPrefix env
  assertStructureFieldsBreakMandatory env
  assertStructureFieldTypeBreakIndentation env
  assertInductiveAlternativesBreakMandatory env
  assertStructInstanceFieldsBreakMandatory env
  assertStructInstanceFieldsBreakMandatoryBetweenFields env
  assertStructInstanceFieldsBreakBalanced env
  assertTypedStructInstanceBreaksBalanced env
  assertStructInstanceFieldBindersPreserved env
  assertStructUpdateWithFieldsBreaks env
  assertTupleBreakBalanced env
  assertAnonymousConstructorBreakBalanced env
  assertExportBreaksLongList env
  assertBangApplicationDiagnostics env

def runCliAndArchitectureTests (env : Lean.Environment) : IO Unit := do
  assertCliParsing
  assertEnvironmentCacheBound env
  assertFormattingExceptionChecks env
  assertCliChecksStillFormatUnlessCheck env
  assertCliFormatsDirectory env
  assertCliFormatsDirectoryRecursively env
  assertCliSkipsHiddenPathsByDefault
  assertCliLoadsImportedSyntax
  assertFmtExecutableConfigured
  assertRendererTraceIncludesPathAndState env
  assertCliFixtureUpdate env
  assertFormatterArchitecture
  assertDeclarationRuleTransparent
  assertMathlibLowRiskSyntaxKindsHaveRules
  assertMissingRuleCheckUsesDispatch env
  assertCheckCommandHasRule env
  assertSyntaxDeclarationsHaveRules env
  assertParserStateUpdatesAfterSyntaxCommands env
  assertCustomBracedTermSyntaxKeepsNestedSourceLayout env
  assertPrefixedTermWrappersHaveRules env
  assertCslibStyleCoreSyntaxHasRules env

#eval
  show IO Unit from do
    let env ← Formatter.defaultEnvironment
    runSyntaxTreeTests env
    runBasicFormattingTests env
    runExpressionAndRendererTests env
    runControlFlowTests env
    runCollectionAndDeclarationTests env
    runCliAndArchitectureTests env

end LeanFmt.Tests
