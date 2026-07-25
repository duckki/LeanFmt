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
  let moduleTree ← SyntaxTree.parseModuleStringWithEnv env source "syntax-tree-where.lean"
  assertEq "syntax tree where reconstruction" source moduleTree.reconstruct

def assertUnifHintChildrenRegrouped : IO Unit := do
  let parameters :=
    SyntaxTree.Tree.node (SyntaxTree.NodeKind.raw `null)
      #[
        .node (.raw `Lean.Parser.Term.implicitBinder) #[],
        .node (.raw `Lean.Parser.Term.explicitBinder) #[]
      ]
  let constraints :=
    SyntaxTree.Tree.node (SyntaxTree.NodeKind.raw `null)
      #[
        .node (.raw `Lean.unifConstraintElem) #[],
        .node (.raw `Lean.unifConstraintElem) #[],
        .node (.raw `Lean.unifConstraintElem) #[]
      ]
  let raw :=
    SyntaxTree.Tree.node
      (SyntaxTree.NodeKind.raw `Lean.«command__Unif_hint____Where_|_-⊢__»)
      #[
        .missing,
        .missing,
        .missing,
        .missing,
        parameters,
        .missing,
        constraints,
        .missing,
        .missing
      ]
  let regrouped := SyntaxTree.regroupTree raw
  let (parametersRegrouped, constraintsTree?) :=
    match regrouped with
    | .node _ children =>
        let parametersRegrouped :=
          match children[4]? with
          | some (SyntaxTree.Tree.node SyntaxTree.NodeKind.signatureParameters binders) =>
              binders.size == 2
          | _ => false
        (parametersRegrouped, children[6]?)
    | _ => (false, none)
  assertTrue "unification hint parameters are grouped as signature parameters"
    parametersRegrouped
  let constraintsTree ←
    match constraintsTree? with
    | some tree@(.node .unifConstraints constraints) =>
        assertTrue "unification hint constraints retain every syntax element"
          (constraints.size == 3)
        pure tree
    | _ => throw <| IO.userError "unification hint constraints were not regrouped"
  let rule ←
    match Formatter.LineBreakRules.ruleFor constraintsTree with
    | some rule => pure rule
    | none => throw <| IO.userError "unification hint constraints have no rule"
  let segment := Formatter.LineBreakRules.Segment.ofTree constraintsTree
  assertTrue "unification hint constraint breaks are mandatory"
    (rule.mandatory {} segment)
  assertTrue "unification hint constraints break between elements"
    (rule.breakPoints {} segment
      == [{ index := 1, indentLevels := 0 }, { index := 2, indentLevels := 0 }])

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
  let moduleTree ← SyntaxTree.parseModuleStringWithEnv env source "quotation-overlap.lean"
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
    Formatter.formatSourceWithEnvDetailed env source "tactic-quotation-antiquotation.lean"
  assertTrue "tactic quotation antiquotation does not fall back" (!result.fellBack)
  assertTrue "tactic quotation antiquotation preserves code"
    (← codePreservedIgnoringWhitespace env source result.formatted)
  assertTextContains "tactic quotation antiquotation prefix stays tight"
    result.formatted "$(Lean.mkIdent `True.intro):term"
  assertTextLacks "tactic quotation antiquotation prefix is not split"
    result.formatted "$\n"
  let elabRulesSource :=
    "elab_rules : tactic\n"
    ++ "  | `(tactic| quoted_tactic) => do\n"
    ++ "    let goal := Lean.mkIdent `True.intro\n"
    ++ "    evalTactic <| ← `(tactic|\n"
    ++ "      refine And.intro ?_ ?_;\n"
    ++ "      exact $goal)\n"
  let elabRulesResult ←
    Formatter.formatSourceWithEnvDetailed env elabRulesSource
      "tactic-quotation-sequence.lean"
  assertTrue "tactic quotation sequence does not fall back" (!elabRulesResult.fellBack)
  assertEq "elab_rules retains its layout-sensitive source" elabRulesSource
    elabRulesResult.formatted
  assertTextContains "tactic quotation sequence keeps its source layout"
    elabRulesResult.formatted
    "`(tactic|\n      refine And.intro ?_ ?_;\n      exact $goal)"
  let elabRulesTree ←
    SyntaxTree.parseModuleStringWithEnv env elabRulesResult.formatted
      "tactic-quotation-sequence-formatted.lean"
  assertTrue "tactic quotation sequence hides nested tactic rule details"
    (Formatter.Diagnostics.missingRuleOccurrencesForModule elabRulesTree).isEmpty
  let movedCommandQuotation :=
    "macro \"emit_two_local_attributes_with_a_long_name\" : command => do\n"
    ++ "  let firstKind := mkIdent `first\n"
    ++ "  let secondKind := mkIdent `second\n"
    ++ "  `(\n"
    ++ "  attribute [local $firstKind] First.declaration\n"
    ++ "  attribute [local $secondKind] Second.declaration\n"
    ++ "  )\n"
  let movedResult ←
    Formatter.formatSourceWithEnvDetailed env movedCommandQuotation
      "moved-command-quotation.lean" { lineWidth := 60 }
  assertTrue "moved command quotation does not fall back" (!movedResult.fellBack)
  assertTrue "moved command quotation preserves code"
    (← codePreservedIgnoringWhitespace env movedCommandQuotation movedResult.formatted)
  assertTextContains "moved command quotation follows its do body"
    movedResult.formatted
    "      `(\n"
  let movedAgain ←
    Formatter.formatSourceWithEnv env movedResult.formatted
      "moved-command-quotation-formatted.lean" { lineWidth := 60 }
  assertEq "moved command quotation is idempotent" movedResult.formatted movedAgain

def assertFullyQualifiedQuotedNamesStayTight (env : Lean.Environment) : IO Unit := do
  let source :=
    "def quotedNames : Std.HashSet Name :=\n"
    ++ "  { ``Lean.Parser.Tactic.tacticSorry, ``Lean.Parser.Tactic.tacticRepeat_,\n"
    ++ "    -- A comment between quoted names must not split either prefix.\n"
    ++ "    ``Lean.Parser.Tactic.tacticSeq1Indented, ``Lean.Parser.Term.byTactic }\n"
  let expected :=
    "def quotedNames : Std.HashSet Name :=\n"
    ++ "  {\n"
    ++ "    ``Lean.Parser.Tactic.tacticSorry,\n"
    ++ "    ``Lean.Parser.Tactic.tacticRepeat_,\n"
    ++ "    -- A comment between quoted names must not split either prefix.\n"
    ++ "    ``Lean.Parser.Tactic.tacticSeq1Indented,\n"
    ++ "    ``Lean.Parser.Term.byTactic\n"
    ++ "  }\n"
  let result ←
    Formatter.formatSourceWithEnvDetailed env source "quoted-names.lean"
      { lineWidth := 60 }
  assertTrue "fully qualified quoted names do not fall back" (!result.fellBack)
  assertTrue "fully qualified quoted names preserve code"
    (← codePreservedIgnoringWhitespace env source result.formatted)
  assertTextLacks "fully qualified quoted name prefix does not gain a space"
    result.formatted "` `"
  assertTextLacks "fully qualified quoted name prefix does not gain a line break"
    result.formatted "`\n`"
  assertEq "comma-separated braced terms use balanced collection layout"
    expected result.formatted
  let formattedAgain ←
    Formatter.formatSourceWithEnv env result.formatted "quoted-names-formatted.lean"
      { lineWidth := 60 }
  assertEq "fully qualified quoted names are idempotent" result.formatted formattedAgain

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

def assertGetElemBracketStaysAttachedAcrossWrap (env : Lean.Environment) : IO Unit := do
  let source :=
    "set_option linter.style.whitespace false in\n"
    ++ "theorem getElemSpacing (l : List α) (n k : Nat) (hk : k < l.length)\n"
    ++ "    : l[k] = ((l.rotate n)[(l.length - n % l.length + k) % l.length]'\n"
    ++ "      ((Nat.mod_lt _ hk).trans_eq (List.length_rotate l n).symm)) := by\n"
    ++ "  sorry\n"
  let formatted ← Formatter.formatSourceWithEnv env source "get-elem-tight-spacing.lean"
  assertTextContains "get-element bracket stays attached to its receiver"
    formatted "(l.rotate n)["
  assertTextLacks "get-element bracket does not become a spaced argument"
    formatted "(l.rotate n) ["
  assertTrue "wrapped get-element notation preserves code"
    (← codePreservedIgnoringWhitespace env source formatted)
  let formattedAgain ←
    Formatter.formatSourceWithEnv env formatted "get-elem-tight-spacing-formatted.lean"
  assertEq "wrapped get-element notation is idempotent" formatted formattedAgain

def assertPostfixSuperscriptSpacingPreservesParse (env : Lean.Environment) : IO Unit := do
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
  let comment := "/-\n" ++ "Copyright line\n\n\n"
  let comment := comment ++ "  Indented author line keeps spacing\n" ++ "-/\n"
  let source := comment ++ "def commentAfterHeader := 0\n"
  let formatted ← Formatter.formatSourceWithEnv env source "block-comment-spacing.lean"
  assertTrue "block comment formatting preserves code"
    (← codePreservedIgnoringWhitespace env source formatted)
  assertTextContains "block comment indentation is preserved" formatted
    "  Indented author line keeps spacing"
  assertTextContains "block comment internal blank lines are preserved"
    formatted "Copyright line\n\n\n  Indented author line"
  let nestedSource :=
    "/-\n" ++ "Outer comment.\n" ++ "/-- Nested documentation comment. -/\n"
    ++ "  Indentation after the nested comment stays unchanged.\n" ++ "-/\n"
    ++ "def nestedCommentAfterHeader := 0\n"
  let nestedFormatted ←
    Formatter.formatSourceWithEnv env nestedSource "nested-block-comment-spacing.lean"
  assertEq "nested block comment whitespace is preserved" nestedSource nestedFormatted

def assertIndentedCommentTriviaDoesNotPadBlankLines : IO Unit := do
  let trivia := "\n\n          -- Search through the local context.\n          "
  let expected := "\n\n    -- Search through the local context.\n    "
  let formatted := Formatter.SpaceRules.commentTriviaForBreak trivia "    "
  assertEq "indented comment trivia leaves blank lines empty" expected formatted
  assertEq "indented comment trivia has no trailing whitespace on completed lines"
    formatted (Formatter.SpaceRules.stripWhitespaceBeforeNewlines formatted)
  let comment := "-- " ++ String.ofList (List.replicate 93 'x')
  let longTrivia := "\n    " ++ comment ++ "\n    "
  let commentIndent :=
    Formatter.spaces <| Formatter.SpaceRules.commentIndentForWidth longTrivia 12 100
  let widthLimited :=
    Formatter.SpaceRules.commentTriviaForBreakWithFollowingIndent longTrivia commentIndent
      "            "
  let widthLimitedExpected := "\n    " ++ comment ++ "\n            "
  assertEq "unwrappable comments retain a fitting indentation"
    widthLimitedExpected widthLimited
  assertTrue "unwrappable comment indentation respects the line width"
    (Formatter.SpaceRules.commentIndentForWidth longTrivia 12 100 == 4)
  let overflowingTrivia := "\n    " ++ comment ++ "xx\n    "
  assertTrue "existing comment overflow is not disguised by deindentation"
    (Formatter.SpaceRules.commentIndentForWidth overflowingTrivia 12 100 == 12)

def assertAtomicTokenRetainsFittingSourceColumn (env : Lean.Environment) : IO Unit := do
  let firstLine := "\"" ++ String.ofList (List.replicate 98 'x')
  let source :=
    "def multilineAtomicText :=\n"
    ++ "  { value :=\n"
    ++ firstLine
    ++ "\n"
    ++ "tail\" }\n"
  let formatted ←
    Formatter.formatSourceWithEnv env source "multiline-atomic-text.lean"
      { lineWidth := 100 }
  assertTextContains "multiline atomic token retains its fitting source column"
    formatted ("\n" ++ firstLine ++ "\n")
  assertTrue "moving a multiline atomic token does not introduce overflow"
    (Formatter.linesFit formatted 100)
  assertTrue "multiline atomic token formatting preserves code"
    (← codePreservedIgnoringWhitespace env source formatted)
  let stringToken := "\"" ++ String.ofList (List.replicate 98 'x') ++ "\""
  let stringSource := "def singleLineAtomicText : String :=\n" ++ stringToken ++ "\n"
  let stringFormatted ←
    Formatter.formatSourceWithEnv env stringSource "single-line-atomic-text.lean"
      { lineWidth := 100 }
  assertTextContains "single-line atomic token retains its fitting parent-relative column"
    stringFormatted ("\n" ++ stringToken ++ "\n")
  assertTrue "single-line atomic token formatting avoids introduced overflow"
    (Formatter.linesFit stringFormatted 100)
  assertTrue "single-line atomic token formatting preserves code"
    (← codePreservedIgnoringWhitespace env stringSource stringFormatted)

def assertDoBodyRetainsSourceLayoutToAvoidOverflow (env : Lean.Environment)
    : IO Unit := do
  let message := "\"" ++ String.ofList (List.replicate 50 'x') ++ "\""
  let source :=
    "def f := do\n"
    ++ "  match value with\n"
    ++ "  | some item =>\n"
    ++ "    if condition then\n"
    ++ "      logError\n"
    ++ "        "
    ++ message
    ++ "\n"
    ++ "  | none => pure ()\n"
  let formatted ←
    Formatter.formatSourceWithEnv env source "do-body-atomic-overflow.lean"
      { lineWidth := 60 }
  assertTrue "do body source layout avoids introduced atomic overflow"
    (Formatter.linesFit formatted 60)
  assertTrue "do body source layout fallback preserves code"
    (← codePreservedIgnoringWhitespace env source formatted)

def assertRegisterOptionValueUsesDeclarationLayout (env : Lean.Environment)
    : IO Unit := do
  let source :=
    "register_option linter.sample : Bool := {\n"
    ++ "  defValue := true\n"
    ++ "  descr := \"A sample option description that should remain within the configured line width.\"\n"
    ++ "}\n"
  let expected :=
    "register_option linter.sample : Bool :=\n"
    ++ "  {\n"
    ++ "    defValue := true\n"
    ++ "    descr :=\n"
    ++ "      \"A sample option description that should remain within the configured line width.\"\n"
    ++ "  }\n"
  let formatted ←
    Formatter.formatSourceWithEnv env source "register-option-layout.lean"
      { lineWidth := 90 }
  assertEq "register_option values use declaration layout" expected formatted
  assertTrue "register_option values stay within the configured width"
    (Formatter.linesFit formatted 90)

def assertAliasCommandRetainsSourceLayout (env : Lean.Environment) : IO Unit := do
  let source :=
    "alias ⟨_root_.Function.Injective.surjective_of_finite,\n"
    ++ "    _root_.Function.Surjective.injective_of_finite⟩ :=\n"
    ++ "  injective_iff_surjective_of_equiv\n"
  let result ←
    Formatter.formatSourceWithEnvDetailed env source "alias-command-layout.lean"
      { lineWidth := 100 }
  assertTrue "alias command source layout does not fall back" (!result.fellBack)
  assertEq "alias command retains its source layout" source result.formatted
  assertTrue "alias command source layout stays within the configured width"
    (Formatter.linesFit result.formatted 100)

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
  assertEq "explicit identifier marker stays tight without source space" ""
    (Formatter.SpaceRules.interTokenWhitespace "@x"
      (syntheticAtomTokenAt "@" 0 1) (syntheticAtomTokenAt "x" 1 2))
  assertEq "at separator preserves source space" " "
    (Formatter.SpaceRules.interTokenWhitespace "@ \"rev\""
      (syntheticAtomTokenAt "@" 0 1) (syntheticAtomTokenAt "\"rev\"" 2 7))
  assertEq "source-adjacent superscript marker stays tight" ""
    (Formatter.SpaceRules.interTokenWhitespace "m⁻¹"
      (syntheticAtomTokenAt "m" 0 1) (syntheticAtomTokenAt "⁻¹" 1 4))
  assertEq "source-spaced modifier notation keeps its boundary" " "
    (Formatter.SpaceRules.interTokenWhitespace "f ⁻¹ᵁ"
      (syntheticAtomTokenAt "f" 0 1) (syntheticAtomTokenAt "⁻¹ᵁ" 2 7))
  assertEq "source space after a custom-syntax marker is preserved before its close" " "
    (Formatter.SpaceRules.interTokenWhitespace "← ]"
      (syntheticAtomTokenAt "←" 0 3) (syntheticAtomTokenAt "]" 4 5))
  assertEq "source space before an ordinary collection close is normalized" ""
    (Formatter.SpaceRules.interTokenWhitespace "value ]"
      (syntheticAtomTokenAt "value" 0 5) (syntheticAtomTokenAt "]" 6 7))
  assertEq "operator-like modifier token gets ordinary spacing" " "
    (Formatter.SpaceRules.spaceBetweenTokens
      (syntheticAtomToken "vec") (syntheticAtomToken "ᵥ*"))

def assertOperatorLikeModifierTokenPreservesParse (env : Lean.Environment) : IO Unit := do
  let source :=
    "def vecMul (left right : Nat) := left + right\n"
    ++ "infixl:70 \" ᵥ* \" => vecMul\n"
    ++ "def value := 1 ᵥ* 2\n"
  let formatted ← Formatter.formatSourceWithEnv env source "operator-like-modifier.lean"
  assertTrue "operator-like modifier token formatting preserves code"
    (← codePreservedIgnoringWhitespace env source formatted)
  assertTextContains "operator-like modifier token keeps left boundary" formatted "1 ᵥ* 2"
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

def assertDocumentedTopLevelDeclarationKeepsBaseIndent (env : Lean.Environment)
    : IO Unit := do
  let source := "variable {R : Type}\n" ++ "\n" ++ "/-- Documented definition. -/\n"
    ++ "noncomputable def documentedTopLevelValue (r : R) : R := r\n"
  let formatted ←
    Formatter.formatSourceWithEnv env source "documented-top-level-declaration.lean"
  assertEq "documented top-level declaration keeps base indent" source formatted

def assertModifiedTopLevelCommandsUseLineBase (env : Lean.Environment) : IO Unit := do
  let source :=
    "private inductive listAligned (relation : α -> β -> Prop) : List α -> List β -> Prop where\n"
    ++ "          | nil : listAligned relation [] []\n"
    ++ "          | cons\n"
    ++ "            : relation left right -> listAligned relation leftRest rightRest\n"
    ++ "              -> listAligned relation (left :: leftRest) (right :: rightRest)\n"
    ++ "\n"
    ++ "private structure privatePair (α β : Type) where\n"
    ++ "          left : α\n"
    ++ "          right : β\n"
  let expected :=
    "private inductive listAligned (relation : α -> β -> Prop) : List α -> List β -> Prop where\n"
    ++ "  | nil : listAligned relation [] []\n"
    ++ "  | cons\n"
    ++ "    : relation left right -> listAligned relation leftRest rightRest\n"
    ++ "      -> listAligned relation (left :: leftRest) (right :: rightRest)\n"
    ++ "\n"
    ++ "private structure privatePair (α β : Type) where\n"
    ++ "  left : α\n"
    ++ "  right : β\n"
  let formatted ←
    Formatter.formatSourceWithEnv env source "modified-top-level-command-base.lean"
  assertEq "modified top-level commands use command line base" expected formatted

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

  let unsealSource :=
    "unseal spectralSequence in\n"
    ++ "theorem unsealedWrapper : True := by\n"
    ++ "  trivial\n"
  let unsealFormatted ←
    Formatter.formatSourceWithEnv env unsealSource "unseal-command-in-wrapper.lean"
  assertEq "unseal command wrapper preserves its break after in"
    unsealSource unsealFormatted
  let unsealTree ←
    SyntaxTree.parseModuleStringWithEnv env unsealFormatted
      "unseal-command-in-wrapper.lean"
  assertTrue "unseal command wrapper has complete rule coverage"
    (Formatter.Diagnostics.missingRuleOccurrencesForModule unsealTree).isEmpty

def assertStackedCommandInWrappersBreakBeforeDeclaration (env : Lean.Environment)
    : IO Unit := do
  let source :=
    "set_option backward.defeqAttrib.useBackward true in\n"
    ++ "set_option backward.isDefEq.respectTransparency false in\n"
    ++ "noncomputable instance : True := trivial\n"
  let expected :=
    "set_option backward.defeqAttrib.useBackward true in\n"
    ++ "set_option backward.isDefEq.respectTransparency false in\n"
    ++ "noncomputable instance : True := trivial\n"
  let formatted ←
    Formatter.formatSourceWithEnv env source "stacked-command-in-wrapper.lean"
  assertEq "stacked command in wrappers break before declaration" expected formatted

def assertLeadingDotPatternConstructorsStayTight (env : Lean.Environment) : IO Unit := do
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
    SyntaxTree.parseModuleStringWithEnv env "def x := f a b\n" "grouped-application.lean"
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

def assertConfigEntriesStaySeparated (env : Lean.Environment) : IO Unit := do
  let source :=
    "import Lean.Elab.ConfigEval\n"
    ++ "\n"
    ++ "declare_core_config_elab elabExample Config where\n"
    ++ "  omit foo\n"
    ++ "  option foo := fun cfg _ => do\n"
    ++ "    pure cfg\n"
  let expected :=
    "import Lean.Elab.ConfigEval\n"
    ++ "\n"
    ++ "declare_core_config_elab elabExample Config where\n"
    ++ "  omit foo\n"
    ++ "  option foo :=\n"
    ++ "    fun cfg _ =>\n"
    ++ "      do\n"
    ++ "        pure cfg\n"
  let formatted ← Formatter.formatSourceWithEnv env source "config-entry-separation.lean"
  assertEq "configuration entries stay separated" expected formatted
  let formattedAgain ←
    Formatter.formatSourceWithEnv env formatted "config-entry-separation-formatted.lean"
  assertEq "configuration entry formatting is idempotent" formatted formattedAgain

def assertImportsStayOnSeparateLines (env : Lean.Environment) : IO Unit := do
  let source :=
    "import GraphQL.Execution\n"
    ++ "import GraphQL.SchemaWellFormedness\n"
    ++ "import GraphQL.Validation\n"
  let formatted ← Formatter.formatSourceWithEnv env source "imports.lean"
  assertEq "imports stay on separate lines" source formatted

def assertModuleHeaderGroupsUseBlankLines (env : Lean.Environment) : IO Unit := do
  let source :=
    "module\n"
    ++ "public import Lean\n"
    ++ "\n"
    ++ "public import Init\n"
    ++ "import Std\n"
    ++ "\n"
    ++ "import Lean.Elab\n"
    ++ "/-! Module documentation -/\n"
    ++ "def value := 0\n"
  let expected :=
    "module\n"
    ++ "\n"
    ++ "public import Lean\n"
    ++ "public import Init\n"
    ++ "\n"
    ++ "import Std\n"
    ++ "import Lean.Elab\n"
    ++ "\n"
    ++ "/-! Module documentation -/\n"
    ++ "\n"
    ++ "def value := 0\n"
  let formatted ← Formatter.formatSourceWithEnv env source "module-header-groups.lean"
  assertEq "module header groups use blank lines" expected formatted

def assertMultilineTopLevelDeclarationsUseBlankLines (env : Lean.Environment)
    : IO Unit := do
  let source :=
    "structure First where\n"
    ++ "  value : Nat -- trailing field comment\n"
    ++ "def one := 1\n"
    ++ "def two := 2\n"
    ++ "structure Second where\n"
    ++ "  value : Nat\n"
    ++ "structure Third where\n"
    ++ "  value : Nat\n"
  let expected :=
    "structure First where\n"
    ++ "  value : Nat -- trailing field comment\n"
    ++ "\n"
    ++ "def one := 1\n"
    ++ "def two := 2\n"
    ++ "\n"
    ++ "structure Second where\n"
    ++ "  value : Nat\n"
    ++ "\n"
    ++ "structure Third where\n"
    ++ "  value : Nat\n"
  let formatted ←
    Formatter.formatSourceWithEnv env source "top-level-declaration-spacing.lean"
  assertEq "multiline top-level declarations use blank lines" expected formatted

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

def assertOpenCommandListBreaksFromOpenColumn (env : Lean.Environment) : IO Unit := do
  let source :=
    "open CategoryTheory ModuleCat MonoidalCategory Limits Functor.LaxMonoidal Functor.OplaxMonoidal TensorProduct\n"
  let expected :=
    "open CategoryTheory ModuleCat MonoidalCategory Limits Functor.LaxMonoidal\n"
    ++ "      Functor.OplaxMonoidal TensorProduct\n"
  let formatted ← Formatter.formatSourceWithEnv env source "open-command-list.lean"
  assertEq "open command list breaks from open column" expected formatted

def assertCommentsDoNotBlockFormatting (env : Lean.Environment) : IO Unit := do
  let source :=
    "/-! Module comment -/\n"
    ++ "def  first : Nat := 0\n"
    ++ "-- keep line comment\n"
    ++ "def commentedDeclarationBody : Nat := -- keep body comment\n"
    ++ "      veryLongIdentifierNameThatPushesTheDefinitionBodyPastTheWidthLimit\n"
  let expected :=
    "/-! Module comment -/\n"
    ++ "\n"
    ++ "def first : Nat := 0\n"
    ++ "\n"
    ++ "-- keep line comment\n"
    ++ "def commentedDeclarationBody : Nat := -- keep body comment\n"
    ++ "  veryLongIdentifierNameThatPushesTheDefinitionBodyPastTheWidthLimit\n"
  let formatted ← Formatter.formatSourceWithEnv env source "comments-formatting.lean"
  assertEq "comments do not block formatting" expected formatted
  let syntaxCommentSource :=
    "/-! Ground-typed normalization smoke tests use `*InputQuery` and `*OutputSnapshot` pairs. -/\n"
    ++ "/-- Declaration documentation keeps  its exact internal whitespace and line shape. -/\n"
    ++ "def documented : Nat := 0\n"
  let syntaxCommentExpected :=
    "/-! Ground-typed normalization smoke tests use `*InputQuery` and `*OutputSnapshot` pairs. -/\n"
    ++ "\n"
    ++ "/-- Declaration documentation keeps  its exact internal whitespace and line shape. -/\n"
    ++ "def documented : Nat := 0\n"
  let syntaxCommentFormatted ←
    Formatter.formatSourceWithEnv env syntaxCommentSource "syntax-comments.lean"
  assertEq "syntax comments preserve contents across command spacing"
    syntaxCommentExpected syntaxCommentFormatted

def assertLeadingCommentsPreserved (env : Lean.Environment) : IO Unit := do
  let source := "-- module comment\n" ++ "\n" ++
    "/- outer /- inner -/ end -/\n" ++ "def commented : Nat := 0\n"
  let formatted ← Formatter.formatSourceWithEnv env source "leading-comments.lean"
  assertEq "leading comments are preserved" source formatted

def assertTrailingLineCommentPreserved (env : Lean.Environment) : IO Unit := do
  let source := "def answer : Nat := 0 -- trailing comment\n"
  let formatted ← Formatter.formatSourceWithEnv env source "trailing-line-comment.lean"
  assertEq "trailing line comment preserved" source formatted

def assertAnonymousConstructorAfterListKeepsSpace (env : Lean.Environment) : IO Unit := do
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
    ++ "\n"
    ++ "@[ext]\n"
    ++ "structure Point where\n"
    ++ "  x : Nat\n"
    ++ "\n"
    ++ "@[derive Repr]\n"
    ++ "inductive Choice where\n"
    ++ "  | left\n"
    ++ "  | right\n"
  let formatted ←
    Formatter.formatSourceWithEnv env source "fitting-attribute-declarations.lean"
  assertEq "attributes stay inline only with single-line declarations" expected formatted

  let multilineSource :=
    "@[inline]\n"
    ++ "def annotatedDefinition : Nat := by\n"
    ++ "  exact 0\n"
    ++ "@[simp]\n"
    ++ "theorem annotatedTheorem : True := by\n"
    ++ "  trivial\n"
    ++ "@[ext]\n"
    ++ "structure AnnotatedStructure where\n"
    ++ "  field : Nat\n"
    ++ "@[derive Repr]\n"
    ++ "inductive AnnotatedInductive where\n"
    ++ "  | constructor\n"
  let multilineFormatted ←
    Formatter.formatSourceWithEnv env multilineSource
      "multiline-attribute-declarations.lean"
  let multilineExpected :=
    "@[inline]\n"
    ++ "def annotatedDefinition : Nat := by\n"
    ++ "  exact 0\n"
    ++ "\n"
    ++ "@[simp]\n"
    ++ "theorem annotatedTheorem : True := by\n"
    ++ "  trivial\n"
    ++ "\n"
    ++ "@[ext]\n"
    ++ "structure AnnotatedStructure where\n"
    ++ "  field : Nat\n"
    ++ "\n"
    ++ "@[derive Repr]\n"
    ++ "inductive AnnotatedInductive where\n"
    ++ "  | constructor\n"
  assertEq "multiline declarations keep attributes on separate lines"
    multilineExpected multilineFormatted

  let inlineMultilineSource :=
    "@[simp] theorem inlineAnnotatedMultilineTheorem : True := by\n" ++ "  trivial\n"
  let inlineMultilineExpected :=
    "@[simp]\n"
    ++ "theorem inlineAnnotatedMultilineTheorem : True := by\n"
    ++ "  trivial\n"
  let inlineMultilineFormatted ←
    Formatter.formatSourceWithEnv env inlineMultilineSource
      "inline-multiline-attribute-declaration.lean"
  assertEq "inline attribute breaks before a multiline command"
    inlineMultilineExpected inlineMultilineFormatted

  let longSource :=
    "@[simp] theorem theoremNameWithEnoughCharactersToRequireAnAttributeHeaderBreak (value : VeryLongInputTypeName) : VeryLongOutputTypeName := proof\n"
  let longExpected :=
    "@[simp]\n"
    ++ "theorem theoremNameWithEnoughCharactersToRequireAnAttributeHeaderBreak\n"
    ++ "    (value : VeryLongInputTypeName)\n"
    ++ "    : VeryLongOutputTypeName :=\n"
    ++ "  proof\n"
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

def assertWhereDeclarationAttributeBreaksBeforeDeclaration (env : Lean.Environment)
    : IO Unit := do
  let source :=
    "syntax (name := helperAttr) \"helper_attr\" ident docComment : attr\n"
    ++ "\n"
    ++ "def repeated (k : Nat) : Nat :=\n"
    ++ "  repeated.go k\n"
    ++ "where\n"
    ++ "  /-- Auxiliary implementation for `repeated`. -/\n"
    ++ "  @[helper_attr helper.go /-- Auxiliary implementation for `helper`. -/]\n"
    ++ "  go (k : Nat) : Nat :=\n"
    ++ "    k\n"
  let expected :=
    "syntax (name := helperAttr) \"helper_attr\" ident docComment : attr\n"
    ++ "\n"
    ++ "def repeated (k : Nat) : Nat :=\n"
    ++ "  repeated.go k\n"
    ++ "where\n"
    ++ "  /-- Auxiliary implementation for `repeated`. -/\n"
    ++ "  @[helper_attr helper.go /-- Auxiliary implementation for `helper`. -/]\n"
    ++ "  go (k : Nat) : Nat := k\n"
  let formatted ←
    Formatter.formatSourceWithEnv env source "where-declaration-attribute.lean"
      { lineWidth := 100 }
  assertEq "where declaration attribute breaks before declaration" expected formatted
  let longSource :=
    "def repeatedLong (k : Nat) : Nat := repeatedLong.go k\n"
    ++ "where\n"
    ++ "  @[inline]\n"
    ++ "  go (n : Nat) : Nat → Nat → Nat :=\n"
    ++ "    veryLongFunctionNameThatForcesTheDeclarationValueToBreak n anotherVeryLongArgumentName\n"
  let longExpected :=
    "def repeatedLong (k : Nat) : Nat :=\n"
    ++ "  repeatedLong.go k\n"
    ++ "where\n"
    ++ "  @[inline]\n"
    ++ "  go (n : Nat) : Nat → Nat → Nat :=\n"
    ++ "    veryLongFunctionNameThatForcesTheDeclarationValueToBreak n anotherVeryLongArgumentName\n"
  let longFormatted ←
    Formatter.formatSourceWithEnv env longSource "long-where-declaration-attribute.lean"
      { lineWidth := 100 }
  assertEq "where declaration breaks its value before its fitting signature"
    longExpected longFormatted

def assertEquationWhereUsesDeclarationBase (env : Lean.Environment) : IO Unit := do
  let source :=
    "def chooseResult : Nat → Nat\n"
    ++ "  | 0 => computeResultWithManyArguments firstArgument secondArgument thirdArgument\n"
    ++ "  | n => computeResultWithManyArguments firstArgument secondArgument n\n"
    ++ "where\n"
    ++ "  computeResultWithManyArguments firstArgument secondArgument thirdArgument := thirdArgument\n"
    ++ "  secondLocalDeclaration value := value\n"
  let expected :=
    "def chooseResult : Nat → Nat\n"
    ++ "  | 0 => computeResultWithManyArguments firstArgument secondArgument thirdArgument\n"
    ++ "  | n => computeResultWithManyArguments firstArgument secondArgument n\n"
    ++ "where\n"
    ++ "  computeResultWithManyArguments firstArgument secondArgument thirdArgument :=\n"
    ++ "    thirdArgument\n"
    ++ "  secondLocalDeclaration value := value\n"
  let formatted ← Formatter.formatSourceWithEnv env source "equation-where-base.lean"
  assertEq "equational declaration where uses command base" expected formatted

def assertSingleLineOriginalAttributeSyntaxFitsInline (env : Lean.Environment)
    : IO Unit := do
  let source :=
    "syntax (name := Mathlib.Tactic.inlineAttribute) \"inline_attribute\" ident : attr\n"
    ++ "\n"
    ++ "def Foo : Nat := 0\n"
    ++ "\n"
    ++ "attribute [inline_attribute Foo] Foo\n"
  let formatted ←
    Formatter.formatSourceWithEnv env source "single-line-original-attribute.lean"
  assertEq "single-line original attribute syntax fits inline" source formatted

def assertCommandAttributeBracketPayloadStaysAttached (env : Lean.Environment)
    : IO Unit := do
  let source :=
    "attribute [local instance] hasColimitsOfShape_of_finallySmall IsFiltered.isSifted FinallySmall.preservesColimitsOfShape_of_isFiltered\n"
  let expected :=
    "attribute [local instance]\n"
    ++ "  hasColimitsOfShape_of_finallySmall IsFiltered.isSifted\n"
    ++ "    FinallySmall.preservesColimitsOfShape_of_isFiltered\n"
  let formatted ←
    Formatter.formatSourceWithEnv env source "command-attribute-bracket-payload.lean"
  assertEq "command attribute keeps bracket payload attached" expected formatted

  let classSource :=
    "structure Normal : Prop where\n"
    ++ "  value : True\n"
    ++ "\n"
    ++ "attribute [class] Normal\n"
  let classFormatted ←
    Formatter.formatSourceWithEnv env classSource "class-command-attribute.lean"
  assertEq "class command attribute preserves its layout" classSource classFormatted
  let classTree ←
    SyntaxTree.parseModuleStringWithEnv env classFormatted "class-command-attribute.lean"
  assertTrue "class command attribute has complete rule coverage"
    (Formatter.Diagnostics.missingRuleOccurrencesForModule classTree).isEmpty

def assertPrivateTheoremModifierStaysOnHeader (env : Lean.Environment) : IO Unit := do
  let source := "private theorem privateTheoremModifier : True := by\n" ++ "  trivial\n"
  let formatted ← Formatter.formatSourceWithEnv env source "private-theorem-modifier.lean"
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

def assertDoReassignArrowHasRule (env : Lean.Environment) : IO Unit := do
  let source :=
    "def reassignArrowExample : IO Unit := do\n"
    ++ "  _ ← pure ()\n"
    ++ "  _ ← pure ()\n"
    ++ "  pure ()\n"
  let formatted ← Formatter.formatSourceWithEnv env source "do-reassign-arrow.lean"
  assertEq "do reassign arrow formatting" source formatted
  let moduleTree ←
    SyntaxTree.parseModuleStringWithEnv env formatted "do-reassign-arrow-formatted.lean"
  assertTrue "do reassign arrow has complete rule coverage"
    (Formatter.Diagnostics.missingRuleOccurrencesForModule moduleTree).isEmpty

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
  let nestedSource :=
    "def nestedDoLetElse (e : Expr) : MetaM (Bool × Expr) := do\n"
    ++ "  try\n"
    ++ "    return (true, e)\n"
    ++ "  catch _ =>\n"
    ++ "    let some e' := e.not? | throwError \"Not a comparison: {e}\"\n"
    ++ "    return (false, e')\n"
  let nestedExpected :=
    "def nestedDoLetElse (e : Expr) : MetaM (Bool × Expr) := do\n"
    ++ "  try\n"
    ++ "    return (true, e)\n"
    ++ "  catch _ =>\n"
    ++ "    let some e' := e.not? | throwError \"Not a comparison: {e}\"\n"
    ++ "    return (false, e')\n"
  let nestedFormatted ←
    Formatter.formatSourceWithEnv env nestedSource "nested-do-let-else.lean"
  assertEq "nested do-let fallback keeps its continuation aligned"
    nestedExpected nestedFormatted
  assertTrue "nested do-let fallback preserves code"
    (← codePreservedIgnoringWhitespace env nestedSource nestedFormatted)
  let multilineFallbackSource :=
    "def multilineFallback : Option Nat := do\n"
    ++ "  let (.some first, .some second) := (some 1, some 2)\n"
    ++ "  | failure\n"
    ++ "  return first + second\n"
  let multilineFallbackFormatted ←
    Formatter.formatSourceWithEnv env multilineFallbackSource
      "multiline-do-let-fallback.lean"
  assertEq "multiline do-let fallback keeps continuation at body base"
    multilineFallbackSource multilineFallbackFormatted
  let multiStatementFallbackSource :=
    "def multiStatementFallback (candidate : Option Nat) : Option Nat := do\n"
    ++ "  let some value := candidate |\n"
    ++ "    if candidate.isNone then reportFailure; return none\n"
    ++ "    throwError \"candidate was rejected\"\n"
    ++ "  return value\n"
  let multiStatementFallbackExpected :=
    "def multiStatementFallback (candidate : Option Nat) : Option Nat := do\n"
    ++ "  let some value := candidate |\n"
    ++ "    if candidate.isNone then\n"
    ++ "      reportFailure; return none\n"
    ++ "    throwError \"candidate was rejected\"\n"
    ++ "  return value\n"
  let multiStatementFallbackResult ←
    Formatter.formatSourceWithEnvDetailed env multiStatementFallbackSource
      "multi-statement-do-let-fallback.lean"
  assertTrue "multi-statement do-let fallback does not fall back"
    (!multiStatementFallbackResult.fellBack)
  assertTrue "multi-statement do-let fallback preserves code"
    (← codePreservedIgnoringWhitespace env multiStatementFallbackSource
        multiStatementFallbackResult.formatted)
  assertEq "multi-statement do-let fallback stays beneath the pipe"
    multiStatementFallbackExpected multiStatementFallbackResult.formatted
  let multiStatementFallbackAgain ←
    Formatter.formatSourceWithEnv env multiStatementFallbackResult.formatted
      "multi-statement-do-let-fallback-formatted.lean"
  assertEq "multi-statement do-let fallback is idempotent"
    multiStatementFallbackResult.formatted multiStatementFallbackAgain

def assertDbgTraceBodyUsesTermBase (env : Lean.Environment) : IO Unit := do
  let source :=
    "def tracedValue (debug : Bool) (value : Nat) : Nat :=\n"
    ++ "  if debug then\n"
    ++ "    dbg_trace s!\"value: {value}\"\n"
    ++ "    value\n"
    ++ "  else\n"
    ++ "    value\n"
  let formatted ← Formatter.formatSourceWithEnv env source "dbg-trace-body.lean"
  assertEq "dbg_trace body stays aligned with dbg_trace" source formatted
  assertTrue "dbg_trace body formatting preserves syntax"
    (← codePreservedIgnoringWhitespace env source formatted)

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

def assertNestedDoLetArrowFallbackKeepsBodyBase (env : Lean.Environment) : IO Unit := do
  let source :=
    "def nestedDoLetArrowFallback (value : Option Nat) : Option Nat := do\n"
    ++ "  go value\n"
    ++ "where\n"
    ++ "  go (value : Option Nat) : Option Nat := do\n"
    ++ "    match value with\n"
    ++ "    | some current =>\n"
    ++ "      let some extracted ← value\n"
    ++ "        | -- Keep the multiline fallback beneath the pipe.\n"
    ++ "          let fallback := current\n"
    ++ "          let some nested ← value | return none\n"
    ++ "          return some (fallback + nested)\n"
    ++ "      return some (extracted + current)\n"
    ++ "    | none => none\n"
  let result ←
    Formatter.formatSourceWithEnvDetailed env source "nested-do-let-arrow-fallback.lean"
  assertTrue "nested do-let arrow fallback does not fall back" (!result.fellBack)
  assertTrue "nested do-let arrow fallback preserves code"
    (← codePreservedIgnoringWhitespace env source result.formatted)
  assertTextContains "nested do-let arrow fallback keeps its body beneath the pipe"
    result.formatted
    ("| -- Keep the multiline fallback beneath the pipe.\n"
      ++ "              let fallback := current\n")
  assertTextContains
    "nested do-let arrow fallback keeps the continuation outside its body"
    result.formatted
    ("              return some (fallback + nested)\n"
      ++ "            return some (extracted + current)\n")
  let formattedAgain ←
    Formatter.formatSourceWithEnv env result.formatted
      "nested-do-let-arrow-fallback-formatted.lean"
  assertEq "nested do-let arrow fallback layout is idempotent"
    result.formatted formattedAgain

def assertLambdaDoLetFallbackBlankContinuationKeepsBase (env : Lean.Environment)
    : IO Unit := do
  let source :=
    "def lambdaDoLetFallback (value : Option Nat) : Option Nat := do\n"
    ++ "  value.elim (pure 0) fun current => do\n"
    ++ "    let some item := value | return none\n"
    ++ "\n"
    ++ "    return some (item + current)\n"
  let result ←
    Formatter.formatSourceWithEnvDetailed env source "lambda-do-let-fallback.lean"
  assertTrue "lambda do-let fallback does not fall back" (!result.fellBack)
  assertTrue "lambda do-let fallback preserves code"
    (← codePreservedIgnoringWhitespace env source result.formatted)
  assertTextContains "lambda do-let continuation stays inside the lambda"
    result.formatted
    ("        let some item := value | return none\n"
      ++ "\n"
      ++ "        return some (item + current)\n")
  let formattedAgain ←
    Formatter.formatSourceWithEnv env result.formatted
      "lambda-do-let-fallback-formatted.lean"
  assertEq "lambda do-let fallback layout is idempotent" result.formatted formattedAgain

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

def assertDoMatchExprAlternativesPreserveBranches (env : Lean.Environment) : IO Unit := do
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
    ++ "\n"
    ++ "def whileAndFinallyExample : IO Unit := do\n"
    ++ "  while keepGoing do\n"
    ++ "    pure ()\n"
    ++ "  try\n"
    ++ "    pure ()\n"
    ++ "  finally\n"
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
    ++ "\n"
    ++ "def whileAndFinallyExample : IO Unit := do\n"
    ++ "  while keepGoing do\n"
    ++ "    pure ()\n"
    ++ "  try\n"
    ++ "    pure ()\n"
    ++ "  finally pure ()\n"
  let formatted ← Formatter.formatSourceWithEnv env source "do-control-wrapper-rules.lean"
  assertEq "do control wrapper rules" expected formatted
  let moduleTree ←
    SyntaxTree.parseModuleStringWithEnv env formatted
      "do-control-wrapper-rules-formatted.lean"
  assertTrue "do control wrappers have complete rule coverage"
    (Formatter.Diagnostics.missingRuleOccurrencesForModule moduleTree).isEmpty

def assertDoTrySuffixFollowsShiftedTry (env : Lean.Environment) : IO Unit := do
  let source :=
    "def tryFinallyAfterAssignment : IO Unit := do\n"
    ++ "  let (firstResultWithLongName, secondResultWithLongName) ← try\n"
    ++ "    computeResults\n"
    ++ "  catch _ =>\n"
    ++ "    fallbackResults\n"
    ++ "  finally\n"
    ++ "    cleanupResults\n"
    ++ "  consumeResults firstResultWithLongName secondResultWithLongName\n"
  let expected :=
    "def tryFinallyAfterAssignment : IO Unit := do\n"
    ++ "  let (firstResultWithLongName, secondResultWithLongName) ←\n"
    ++ "    try\n"
    ++ "      computeResults\n"
    ++ "    catch _ =>\n"
    ++ "      fallbackResults\n"
    ++ "    finally cleanupResults\n"
    ++ "  consumeResults firstResultWithLongName\n"
    ++ "    secondResultWithLongName\n"
  let formatted ←
    Formatter.formatSourceWithEnv env source
      "do-try-suffix-shift.lean" { lineWidth := 60 }
  assertEq "do-try suffix follows a shifted try" expected formatted
  assertTrue "shifted do-try suffix preserves code"
    (← codePreservedIgnoringWhitespace env source formatted)
  let formattedAgain ←
    Formatter.formatSourceWithEnv env formatted
      "do-try-suffix-shift-formatted.lean" { lineWidth := 60 }
  assertEq "shifted do-try suffix is idempotent" formatted formattedAgain

def assertReturnDoesNotBreakBeforeValue (env : Lean.Environment) : IO Unit := do
  let source :=
    "def returnAnonymousConstructor : Result := do\n"
    ++ "  return ⟨veryLongFunctionNameForReturnConstructor firstArgument secondArgument, anotherVeryLongFunctionNameForReturnConstructor thirdArgument fourthArgument⟩\n"
  let formatted ← Formatter.formatSourceWithEnv env source "return-constructor-break.lean"
  assertTextLacks "return keeps value on same line" formatted "return\n"
  let _ ←
    SyntaxTree.parseModuleStringWithEnv env formatted "return-constructor-break.lean"

def assertShowAndDoWrapperRules (env : Lean.Environment) : IO Unit := do
  assertShowFromBreaksLikeAssignment env
  assertDoControlWrapperRules env
  assertDoTrySuffixFollowsShiftedTry env
  assertReturnDoesNotBreakBeforeValue env
  assertDoLetElseBreaks env
  assertDbgTraceBodyUsesTermBase env
  assertDoLetArrowFallbackBreaksBeforeContinuation env
  assertNestedDoLetArrowFallbackKeepsBodyBase env
  assertLambdaDoLetFallbackBlankContinuationKeepsBase env
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
  assertTextContains "pipe projection chain keeps dot member attached" formatted "|>.symm"
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

def assertDefinitionDerivingStaysOnOwnLine (env : Lean.Environment) : IO Unit := do
  let source :=
    "def DerivedAlias : Type :=\n" ++ "  Nat\n" ++ "deriving Repr, Inhabited\n"
  let formatted ←
    Formatter.formatSourceWithEnv env source "definition-deriving-own-line.lean"
  assertEq "definition deriving stays on own line" source formatted

def assertLongDerivingClauseFlowsClasses (env : Lean.Environment) : IO Unit := do
  let source :=
    "def anodyneExtensions : MorphismProperty SSet := fibrations.llp\n"
    ++ "deriving IsMultiplicative, RespectsIso, IsStableUnderCobaseChange, IsStableUnderRetracts, IsStableUnderTransfiniteComposition, IsStableUnderCoproducts\n"
  let expected :=
    "def anodyneExtensions : MorphismProperty SSet :=\n"
    ++ "  fibrations.llp\n"
    ++ "deriving IsMultiplicative, RespectsIso, IsStableUnderCobaseChange, IsStableUnderRetracts,\n"
    ++ "  IsStableUnderTransfiniteComposition, IsStableUnderCoproducts\n"
  let formatted ← Formatter.formatSourceWithEnv env source "long-deriving-clause.lean"
  assertEq "long deriving clause flows classes" expected formatted

def assertLongDerivingInstanceFlowsClasses (env : Lean.Environment) : IO Unit := do
  let source :=
    "deriving instance\n"
    ++ "  Nontrivial, Add, Sub, LE, LT, Bot, Preorder, LinearOrder, OrderTop, OrderBot, WellFoundedLT, SuccOrder, AddMonoidWithOne, CommSemiring, LinearOrderedAddCommMonoidWithTop\n"
    ++ "for ENat\n"
  let expected :=
    "deriving instance\n"
    ++ "  Nontrivial, Add, Sub, LE, LT, Bot, Preorder, LinearOrder, OrderTop, OrderBot,\n"
    ++ "    WellFoundedLT, SuccOrder, AddMonoidWithOne, CommSemiring,\n"
    ++ "    LinearOrderedAddCommMonoidWithTop\n"
    ++ "for ENat\n"
  let formatted ← Formatter.formatSourceWithEnv env source "long-deriving-instance.lean"
  assertEq "long deriving instance flows classes" expected formatted

def assertMatchMotiveUsesTransparentRule (env : Lean.Environment) : IO Unit := do
  let source :=
    "def motiveExample (x : Nat) : Nat :=\n"
    ++ "  match (motive := fun _ => Nat) x with\n"
    ++ "  | value => value\n"
  let formatted ← Formatter.formatSourceWithEnv env source "match-motive.lean"
  assertEq "match motive formatting" source formatted
  let moduleTree ←
    SyntaxTree.parseModuleStringWithEnv env formatted "match-motive-formatted.lean"
  assertTrue "match motive syntax has no missing rule"
    (Formatter.Diagnostics.missingRuleOccurrencesForModule moduleTree).isEmpty

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

def assertPrivateStructureFieldsUseCommandBase (env : Lean.Environment) : IO Unit := do
  let source :=
    "private structure BadChar (N : Nat) where\n"
    ++ "  /-- The primary field. -/\n"
    ++ "  value : Nat\n"
    ++ "  firstProof : value = value\n"
    ++ "  secondProof : value = value\n"
  let formatted ←
    Formatter.formatSourceWithEnv env source "private-structure-field-base.lean"
  assertEq "private structure fields use the command base" source formatted
  let formattedAgain ←
    Formatter.formatSourceWithEnv env formatted
      "private-structure-field-base-formatted.lean"
  assertEq "private structure field formatting is idempotent" formatted formattedAgain

def assertStructureFieldProofBreaksAfterAssignment (env : Lean.Environment)
    : IO Unit := do
  let source :=
    "structure Hom where\n"
    ++ "  naturality : VeryLongTypeNameForStructureFieldDefaultProofLayoutTestingAndMoreCharacters := by exact 0\n"
  let expected :=
    "structure Hom where\n"
    ++ "  naturality\n"
    ++ "    : VeryLongTypeNameForStructureFieldDefaultProofLayoutTestingAndMoreCharacters :=\n"
    ++ "      by exact 0\n"
  let formatted ←
    Formatter.formatSourceWithEnv env source "structure-field-proof-break.lean"
  assertEq "structure field proof breaks after assignment" expected formatted

def assertStructureInstanceMethodBindersFlow (env : Lean.Environment) : IO Unit := do
  let source :=
    "class LongMethod (F : Type) where\n"
    ++ "  method (a : F) (ι : Type) [Inhabited ι] (c : ι → F) (hc : c = c)\n"
    ++ "    (u : ι → F) (v : F) (h : a = a) : F\n"
    ++ "\n"
    ++ "instance {F : Type} [Inhabited F] : LongMethod F where\n"
    ++ "  method (a : F) (ι : Type) [Inhabited ι] (c : ι → F) (hc : c = c) (u : ι → F) (v : F) (h : a = a) := a\n"
  let formatted ←
    Formatter.formatSourceWithEnv env source "structure-instance-method-binders.lean"
      { lineWidth := 100 }
  assertTrue "structure instance method binder formatting preserves code"
    (← codePreservedIgnoringWhitespace env source formatted)
  assertTextContains "structure instance method binders flow before deep terms"
    formatted "\n      (h : a = a)"
  let moduleTree ←
    SyntaxTree.parseModuleStringWithEnv env formatted
      "structure-instance-method-binders-formatted.lean"
  assertTrue "structure instance method formatting avoids overflow"
    (Formatter.Diagnostics.overflowOccurrences moduleTree { lineWidth := 100 }).isEmpty
  let formattedAgain ←
    Formatter.formatSourceWithEnv env formatted
      "structure-instance-method-binders-formatted.lean" { lineWidth := 100 }
  assertEq "structure instance method binder formatting is idempotent"
    formatted formattedAgain

def assertBinderDefaultValueUsesBinderBase (env : Lean.Environment) : IO Unit := do
  let source :=
    "def withDefault (H : ∀ {a b c d : Nat}, a = b → b = c → c = d → Nat := fun {_ _ _ _} h₁ h₂ h₃ => veryLongFunctionNameForDefaultBinder h₁ h₂ h₃) : Nat := 0\n"
  let formatted ←
    Formatter.formatSourceWithEnv env source "binder-default-value-base.lean"
      { lineWidth := 100 }
  assertTrue "binder default value formatting preserves code"
    (← codePreservedIgnoringWhitespace env source formatted)
  assertTextContains "binder default value breaks from the binder base"
    formatted " :=\n        fun {_ _ _ _}"
  let moduleTree ←
    SyntaxTree.parseModuleStringWithEnv env formatted
      "binder-default-value-base-formatted.lean"
  assertTrue "binder default value formatting avoids overflow"
    (Formatter.Diagnostics.overflowOccurrences moduleTree { lineWidth := 100 }).isEmpty
  let formattedAgain ←
    Formatter.formatSourceWithEnv env formatted
      "binder-default-value-base-formatted.lean" { lineWidth := 100 }
  assertEq "binder default value formatting is idempotent" formatted formattedAgain

def assertParenthesizedStructureDefaultUsesFieldBase (env : Lean.Environment)
    : IO Unit := do
  let source :=
    "structure Child extends Parent where\n"
    ++ "  inheritedField {a} u ha :=\n"
    ++ "    (by exact veryLongProofTermNameWithEnoughCharactersForBreakingAndMoreCharactersToExceedLineWidth)\n"
  let expected :=
    "structure Child\n"
    ++ "    extends Parent where\n"
    ++ "  inheritedField {a} u ha :=\n"
    ++ "    (by\n"
    ++ "      exact veryLongProofTermNameWithEnoughCharactersForBreakingAndMoreCharactersToExceedLineWidth)\n"
  let formatted ←
    Formatter.formatSourceWithEnv env source "parenthesized-structure-default.lean"
  assertEq "parenthesized structure default uses field base" expected formatted
  let formattedAgain ←
    Formatter.formatSourceWithEnv env formatted
      "parenthesized-structure-default-formatted.lean"
  assertEq "parenthesized structure default formatting is idempotent"
    formatted formattedAgain

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

def assertStructureValueWhereFormattingKeepsSuffix (env : Lean.Environment)
    : IO Unit := do
  let source :=
    "structure Result where\n"
    ++ "  field : Nat\n"
    ++ "\n"
    ++ "def make : Result where\n"
    ++ "  field := helper\n"
    ++ "where\n"
    ++ "  helper := 1\n"
  let result ←
    Formatter.formatSourceWithEnvDetailed env source
      "structure-value-where-formatting.lean"
  assertTrue "structure-value where formatting does not fall back" (!result.fellBack)
  assertEq "structure-value where formatting keeps suffix" source result.formatted
  let formattedAgain ←
    Formatter.formatSourceWithEnv env result.formatted
      "structure-value-where-formatting-formatted.lean"
  assertEq "structure-value where formatting is idempotent"
    result.formatted formattedAgain

def assertWhereFinallyKeepsHeaderAndProofBody (env : Lean.Environment) : IO Unit := do
  let source :=
    "def fillHole : Nat :=\n" ++ "  ?_\n" ++ "where finally\n" ++ "  exact 0\n"
  let result ← Formatter.formatSourceWithEnvDetailed env source "where-finally.lean"
  assertTrue "where finally does not fall back" (!result.fellBack)
  assertTextContains "where finally stays on one line" result.formatted "where finally\n"
  assertTextContains "where finally proof body remains intact"
    result.formatted "finally\n  exact 0\n"
  assertTrue "where finally preserves code"
    (← codePreservedIgnoringWhitespace env source result.formatted)
  let moduleTree ←
    SyntaxTree.parseModuleStringWithEnv env result.formatted
      "where-finally-formatted.lean"
  assertTrue "where finally regroups its tactic as a proof body"
    (moduleTree.tree.containsNodeKind .proofBody)
  assertTrue "where finally has complete rule coverage"
    (Formatter.Diagnostics.missingRuleOccurrencesForModule moduleTree).isEmpty
  let formattedAgain ←
    Formatter.formatSourceWithEnv env result.formatted
      "where-finally-formatted-again.lean"
  assertEq "where finally is idempotent" result.formatted formattedAgain

def assertProofBodyUntouched (env : Lean.Environment) : IO Unit := do
  let source :=
    "theorem proofBodyUntouched : True := by\n" ++ "  exact\n" ++ "    True.intro\n"
  let formatted ← Formatter.formatSourceWithEnv env source "proof-body-untouched.lean"
  assertEq "proof body untouched" source formatted

def assertMovedProofBodiesKeepRelativeIndentation (env : Lean.Environment) : IO Unit := do
  let lambdaSource :=
    "def proofUnderMovedLambda :=\n"
    ++ "  fun ⟨x, hx⟩ =>\n"
    ++ "  have h : True := by\n"
    ++ "    /- Keep this\n"
    ++ "         internal comment indentation. -/\n"
    ++ "    exact True.intro\n"
    ++ "  h\n"
  let lambdaExpected :=
    "def proofUnderMovedLambda :=\n"
    ++ "  fun ⟨x, hx⟩ =>\n"
    ++ "    have h : True := by\n"
    ++ "      /- Keep this\n"
    ++ "         internal comment indentation. -/\n"
    ++ "      exact True.intro\n"
    ++ "    h\n"
  let lambdaFormatted ←
    Formatter.formatSourceWithEnv env lambdaSource "proof-under-moved-lambda.lean"
  assertEq "proof body follows a moved lambda body" lambdaExpected lambdaFormatted

  let matchSource :=
    "def proofUnderMovedMatchAlternative :=\n"
    ++ "  le_antisymm veryLongLeftProofNameWithEnoughCharactersToForceTheOperatorToBreak\n"
    ++ "    veryLongRightProofNameWithEnoughCharactersToForceTheOperatorToBreak <|\n"
    ++ "    match condition with\n"
    ++ "    | true => by\n"
    ++ "      exact True.intro\n"
    ++ "    | false => by\n"
    ++ "      exact True.intro\n"
  let matchFormatted ←
    Formatter.formatSourceWithEnv env matchSource
      "proof-under-moved-match-alternative.lean"
  assertTrue "match alternative proof outer layout changes"
    (matchFormatted != matchSource)
  assertTrue "moved match alternative proof preserves code"
    (← codePreservedIgnoringWhitespace env matchSource matchFormatted)
  let matchFormattedAgain ←
    Formatter.formatSourceWithEnv env matchFormatted
      "proof-under-moved-match-alternative-formatted.lean"
  assertEq "moved match alternative proof is idempotent"
    matchFormatted matchFormattedAgain

  let whereSource :=
    "private theorem outer\n"
    ++ "    : ∀ values : List Nat, True\n"
    ++ "  | [] => by\n"
    ++ "      trivial\n"
    ++ "  | value :: rest => by\n"
    ++ "      exact True.intro\n"
    ++ "  where\n"
    ++ "    helper (target : Nat) : ∀ values : List Nat, True\n"
    ++ "      | [] => by\n"
    ++ "          trivial\n"
    ++ "      | candidate :: rest => by\n"
    ++ "          by_cases hmatch : target = candidate\n"
    ++ "          · trivial\n"
    ++ "          · trivial\n"
  let whereExpected :=
    "private theorem outer : ∀ values : List Nat, True\n"
    ++ "  | [] => by\n"
    ++ "      trivial\n"
    ++ "  | value :: rest => by\n"
    ++ "      exact True.intro\n"
    ++ "where\n"
    ++ "  helper (target : Nat) : ∀ values : List Nat, True\n"
    ++ "    | [] => by\n"
    ++ "        trivial\n"
    ++ "    | candidate :: rest => by\n"
    ++ "        by_cases hmatch : target = candidate\n"
    ++ "        · trivial\n"
    ++ "        · trivial\n"
  let whereFormatted ←
    Formatter.formatSourceWithEnv env whereSource
      "proof-under-moved-where-declaration.lean"
  assertEq "proof bodies follow moved where declarations" whereExpected whereFormatted
  assertTrue "moved where declaration proof preserves code"
    (← codePreservedIgnoringWhitespace env whereSource whereFormatted)
  let whereFormattedAgain ←
    Formatter.formatSourceWithEnv env whereFormatted
      "proof-under-moved-where-declaration-formatted.lean"
  assertEq "moved where declaration proof is idempotent"
    whereFormatted whereFormattedAgain

def assertMovedInlineProofBodiesRemainParseable (env : Lean.Environment) : IO Unit := do
  let source :=
    "theorem nestedInlineProofs (left right : True) : True :=\n"
    ++ "  And.left\n"
    ++ "    (And.intro\n"
    ++ "      (by exact left)\n"
    ++ "      (And.intro\n"
    ++ "        (by rw [show True = True from rfl]\n"
    ++ "            exact left)\n"
    ++ "        (by rw [show True = True from rfl]\n"
    ++ "            exact right)))\n"
  let result ←
    Formatter.formatSourceWithEnvDetailed env source "moved-inline-proof-body.lean"
      { lineWidth := 100 }
  assertTrue "moved inline proof body does not fall back" (!result.fellBack)
  assertTrue "moved inline proof body preserves code"
    (← codePreservedIgnoringWhitespace env source result.formatted)
  assertTextContains "first moved inline proof body remains present"
    result.formatted "exact left"
  assertTextContains "second moved inline proof body remains present"
    result.formatted "exact right"
  let declarationSource :=
    "theorem inlineMultilineProofWithEnoughHeaderCharactersToRequireWrapping (h : True) : True := by classical\n"
    ++ "  exact h\n"
  let declarationExpected :=
    "theorem inlineMultilineProofWithEnoughHeaderCharactersToRequireWrapping (h : True)\n"
    ++ "    : True := by classical\n"
    ++ "  exact h\n"
  let declarationResult ←
    Formatter.formatSourceWithEnvDetailed env declarationSource
      "inline-multiline-declaration-proof.lean"
  assertTrue "inline multiline declaration proof does not fall back"
    (!declarationResult.fellBack)
  assertEq "inline multiline declaration proof keeps continuation indentation"
    declarationExpected declarationResult.formatted
  assertTrue "inline multiline declaration proof preserves code"
    (← codePreservedIgnoringWhitespace env declarationSource declarationResult.formatted)
  let declarationAgain ←
    Formatter.formatSourceWithEnv env declarationResult.formatted
      "inline-multiline-declaration-proof-formatted.lean"
  assertEq "inline multiline declaration proof is idempotent"
    declarationResult.formatted declarationAgain

def assertShowProofTermUntouched (env : Lean.Environment) : IO Unit := do
  let source := "#check (show True by\n" ++ "  trivial)\n"
  let formatted ← Formatter.formatSourceWithEnv env source "show-proof-term.lean"
  assertTrue "show proof term preserves code"
    (← codePreservedIgnoringWhitespace env source formatted)
  assertTextContains "show proof term keeps tactic body break" formatted "show True by\n"
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
    Formatter.formatSourceWithEnv env source "theorem-equation-proof-body-untouched.lean"
  assertEq "theorem equation proof body untouched" source formatted

def assertInstanceEquationArmsUseDeclarationBase (env : Lean.Environment) : IO Unit := do
  let source :=
    "instance All.decidable {P : α → Prop} : (t : Ordnode α) → [DecidablePred P] → Decidable (All P t)\n"
    ++ "  | nil => isTrue trivial\n"
    ++ "  | node _ l m r =>\n"
    ++ "    have : Decidable (All P l) := All.decidable l\n"
    ++ "    inferInstanceAs <| Decidable (All P l ∧ P m)\n"
  let expected :=
    "instance All.decidable {P : α → Prop} : (t : Ordnode α) → [DecidablePred P] → Decidable (All P t)\n"
    ++ "  | nil => isTrue trivial\n"
    ++ "  | node _ l m r =>\n"
    ++ "      have : Decidable (All P l) := All.decidable l\n"
    ++ "      inferInstanceAs <| Decidable (All P l ∧ P m)\n"
  let formatted ←
    Formatter.formatSourceWithEnv env source "instance-equation-declaration-base.lean"
      { lineWidth := 100 }
  assertEq "instance equation arms use the declaration base" expected formatted

def assertDefinitionContainingProofUntouched (env : Lean.Environment) : IO Unit := do
  let source :=
    "structure ProofRecord where\n"
    ++ "  proof : True\n"
    ++ "\n"
    ++ "def proofRecordBody : ProofRecord where\n"
    ++ "  proof := by\n"
    ++ "    trivial\n"
  let formatted ←
    Formatter.formatSourceWithEnv env source "definition-containing-proof-untouched.lean"
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

def assertTerminationProofSuffixDoesNotAccumulateIndent (env : Lean.Environment)
    : IO Unit := do
  let source :=
    "def toTree (p : DyckWord) : BinaryTree Unit :=\n"
    ++ "  if p = 0 then nil else p.insidePart.toTree △ p.outsidePart.toTree\n"
    ++ "termination_by p.semilength\n"
    ++ "decreasing_by exacts [semilength_insidePart_lt ‹_›, semilength_outsidePart_lt ‹_›]\n"
  let formatted ←
    Formatter.formatSourceWithEnv env source "termination-proof-suffix-stable-indent.lean"
  assertEq "termination proof suffix keeps its source indentation" source formatted
  let formattedAgain ←
    Formatter.formatSourceWithEnv env formatted
      "termination-proof-suffix-stable-indent-formatted.lean"
  assertEq "termination proof suffix indentation is idempotent" formatted formattedAgain

def assertTerminationByBreakPriority (env : Lean.Environment) : IO Unit := do
  let source :=
    "def flatTermination := value\n"
    ++ "termination_by n => n\n"
    ++ "\n"
    ++ "def bodyBreakTermination := value\n"
    ++ "termination_by leftPattern rightPattern => veryLongTerminationMeasureName\n"
    ++ "\n"
    ++ "def patternFlowTermination := value\n"
    ++ "termination_by firstPattern secondPattern thirdPattern fourthPattern => measure\n"
  let expected :=
    "def flatTermination :=\n"
    ++ "  value\n"
    ++ "termination_by n => n\n"
    ++ "\n"
    ++ "def bodyBreakTermination :=\n"
    ++ "  value\n"
    ++ "termination_by leftPattern rightPattern =>\n"
    ++ "  veryLongTerminationMeasureName\n"
    ++ "\n"
    ++ "def patternFlowTermination :=\n"
    ++ "  value\n"
    ++ "termination_by firstPattern secondPattern thirdPattern\n"
    ++ "    fourthPattern =>\n"
    ++ "  measure\n"
  let result ←
    Formatter.formatSourceWithEnvDetailed env source "termination-by-break-priority.lean"
      { lineWidth := 60 }
  assertTrue "termination_by break priority does not fall back" (!result.fellBack)
  assertEq "termination_by breaks body before flowing patterns" expected result.formatted
  assertTrue "termination_by break priority preserves code"
    (← codePreservedIgnoringWhitespace env source result.formatted)
  let formattedAgain ←
    Formatter.formatSourceWithEnv env result.formatted
      "termination-by-break-priority-formatted.lean" { lineWidth := 60 }
  assertEq "termination_by break priority is idempotent" result.formatted formattedAgain

def assertTerminationClausesUseDeclarationBase (env : Lean.Environment) : IO Unit := do
  let simpleSource :=
    "def outer (n : Nat) : Nat :=\n"
    ++ "  helper n\n"
    ++ "  termination_by n\n"
    ++ "  decreasing_by\n"
    ++ "    exact outerProof\n"
    ++ "  where\n"
    ++ "    helper (n : Nat) : Nat := helper (n - 1)\n"
    ++ "    termination_by n\n"
    ++ "    decreasing_by exact helperProof\n"
  let simpleExpected :=
    "def outer (n : Nat) : Nat :=\n"
    ++ "  helper n\n"
    ++ "termination_by n\n"
    ++ "decreasing_by\n"
    ++ "  exact outerProof\n"
    ++ "where\n"
    ++ "  helper (n : Nat) : Nat := helper (n - 1)\n"
    ++ "  termination_by n\n"
    ++ "  decreasing_by exact helperProof\n"
  let simpleResult ←
    Formatter.formatSourceWithEnvDetailed env simpleSource
      "termination-clauses-declaration-base.lean"
  assertTrue "termination clause alignment does not fall back" (!simpleResult.fellBack)
  assertEq "termination clauses use their declaration base"
    simpleExpected simpleResult.formatted
  assertTrue "termination clause alignment preserves code"
    (← codePreservedIgnoringWhitespace env simpleSource simpleResult.formatted)
  let moduleTree ←
    SyntaxTree.parseModuleStringWithEnv env simpleResult.formatted
      "termination-clauses-declaration-base-formatted.lean"
  assertTrue "decreasing clause tactic is a protected proof body"
    (moduleTree.tree.containsNodeKind .proofBody)
  assertTrue "termination clauses have complete rule coverage"
    (Formatter.Diagnostics.missingRuleOccurrencesForModule moduleTree).isEmpty
  let formattedAgain ←
    Formatter.formatSourceWithEnv env simpleResult.formatted
      "termination-clauses-declaration-base-formatted-again.lean"
  assertEq "termination clause alignment is idempotent"
    simpleResult.formatted formattedAgain

  let equationSource :=
    "def countdown : Nat -> Nat\n"
    ++ "  | 0 => 0\n"
    ++ "  | n + 1 => countdown n\n"
    ++ "  termination_by n => n\n"
    ++ "  decreasing_by\n"
    ++ "    exact equationProof\n"
  let equationExpected :=
    "def countdown : Nat -> Nat\n"
    ++ "  | 0 => 0\n"
    ++ "  | n + 1 => countdown n\n"
    ++ "termination_by n => n\n"
    ++ "decreasing_by\n"
    ++ "  exact equationProof\n"
  let equationResult ←
    Formatter.formatSourceWithEnvDetailed env equationSource
      "equation-termination-clauses.lean"
  assertTrue "equation termination clauses do not fall back" (!equationResult.fellBack)
  assertEq "equation termination clauses use their declaration base"
    equationExpected equationResult.formatted
  assertTrue "equation termination clause alignment preserves code"
    (← codePreservedIgnoringWhitespace env equationSource equationResult.formatted)
  let equationFormattedAgain ←
    Formatter.formatSourceWithEnv env equationResult.formatted
      "equation-termination-clauses-formatted.lean"
  assertEq "equation termination clause alignment is idempotent"
    equationResult.formatted equationFormattedAgain

  let parameterSource :=
    "def recurse : Nat := recurse\n"
    ++ "termination_by\n"
    ++ "  _schema _variableDefinitions fragments _parentType selection _field _hvalid _hbodies _hfield =>\n"
    ++ "  (fragments.length, sizeOf selection, 0)\n"
    ++ "decreasing_by exact proof\n"
  let parameterExpected :=
    "def recurse : Nat :=\n"
    ++ "  recurse\n"
    ++ "termination_by _schema _variableDefinitions fragments _parentType selection _field _hvalid\n"
    ++ "    _hbodies _hfield =>\n"
    ++ "  (fragments.length, sizeOf selection, 0)\n"
    ++ "decreasing_by exact proof\n"
  let parameterResult ←
    Formatter.formatSourceWithEnvDetailed env parameterSource
      "termination-clause-parameters.lean"
  assertTrue "termination clause parameters do not fall back" (!parameterResult.fellBack)
  assertEq "termination clause parameters wrap before the final parameter"
    parameterExpected parameterResult.formatted
  assertTrue "termination clause parameter wrapping preserves code"
    (← codePreservedIgnoringWhitespace env parameterSource parameterResult.formatted)
  let parameterModule ←
    SyntaxTree.parseModuleStringWithEnv env parameterResult.formatted
      "termination-clause-parameters-formatted.lean"
  assertTrue "termination clause parameter wrapping has no overflow"
    (Formatter.Diagnostics.overflowOccurrences parameterModule).isEmpty
  assertTrue "termination clause parameters have complete rule coverage"
    (Formatter.Diagnostics.missingRuleOccurrencesForModule parameterModule).isEmpty
  let parametersFormattedAgain ←
    Formatter.formatSourceWithEnv env parameterResult.formatted
      "termination-clause-parameters-formatted-again.lean"
  assertEq "termination clause parameter wrapping is idempotent"
    parameterResult.formatted parametersFormattedAgain

  let shortParameterSource :=
    "def shortRecurse : Nat := shortRecurse\n"
    ++ "termination_by _boolCase selectionSet =>\n"
    ++ "  SelectionSet.size selectionSet\n"
    ++ "decreasing_by exact proof\n"
  let shortParameterExpected :=
    "def shortRecurse : Nat :=\n"
    ++ "  shortRecurse\n"
    ++ "termination_by _boolCase selectionSet =>\n"
    ++ "  SelectionSet.size selectionSet\n"
    ++ "decreasing_by exact proof\n"
  let shortParameterFormatted ←
    Formatter.formatSourceWithEnv env shortParameterSource
      "short-termination-clause-parameters.lean"
  assertEq "short termination clause parameters remain after the keyword"
    shortParameterExpected shortParameterFormatted

  let letRecSource :=
    "def localCountdown (n : Nat) : Nat :=\n"
    ++ "  let rec go (n : Nat) : Nat :=\n"
    ++ "    if n = 0 then 0 else go (n - 1)\n"
    ++ "      termination_by n\n"
    ++ "      decreasing_by\n"
    ++ "        exact localProof\n"
    ++ "  go n\n"
  let letRecExpected :=
    "def localCountdown (n : Nat) : Nat :=\n"
    ++ "  let rec go (n : Nat) : Nat := if n = 0 then 0 else go (n - 1)\n"
    ++ "    termination_by n\n"
    ++ "    decreasing_by\n"
    ++ "      exact localProof\n"
    ++ "  go n\n"
  let letRecResult ←
    Formatter.formatSourceWithEnvDetailed env letRecSource
      "let-rec-termination-clauses.lean"
  assertTrue "let-rec termination clauses do not fall back" (!letRecResult.fellBack)
  assertEq "let-rec termination clauses use the local declaration base"
    letRecExpected letRecResult.formatted
  assertTrue "let-rec termination clause alignment preserves code"
    (← codePreservedIgnoringWhitespace env letRecSource letRecResult.formatted)
  let letRecFormattedAgain ←
    Formatter.formatSourceWithEnv env letRecResult.formatted
      "let-rec-termination-clauses-formatted.lean"
  assertEq "let-rec termination clause alignment is idempotent"
    letRecResult.formatted letRecFormattedAgain

  let mutualSource :=
    "mutual\n"
    ++ "  @[implicit_reducible]\n"
    ++ "  def first : Nat → Nat\n"
    ++ "    | 0 => 0\n"
    ++ "    | n + 1 => second n\n"
    ++ "  termination_by n => n\n"
    ++ "  @[implicit_reducible]\n"
    ++ "  def second : Nat → Nat\n"
    ++ "    | 0 => 0\n"
    ++ "    | n + 1 => third n\n"
    ++ "  termination_by n => n\n"
    ++ "  @[implicit_reducible]\n"
    ++ "  def third : Nat → Nat\n"
    ++ "    | 0 => 0\n"
    ++ "    | n + 1 => first n\n"
    ++ "  termination_by n => n\n"
    ++ "end\n"
  let mutualResult ←
    Formatter.formatSourceWithEnvDetailed env mutualSource
      "mutual-termination-clauses.lean"
  assertTrue "mutual termination clauses do not fall back" (!mutualResult.fellBack)
  assertEq "mutual declarations keep their shared body base"
    mutualSource mutualResult.formatted
  assertTrue "mutual termination clause alignment preserves code"
    (← codePreservedIgnoringWhitespace env mutualSource mutualResult.formatted)
  let mutualModule ←
    SyntaxTree.parseModuleStringWithEnv env mutualResult.formatted
      "mutual-termination-clauses-formatted.lean"
  assertTrue "mutual termination clauses avoid overflow"
    (Formatter.Diagnostics.overflowOccurrences mutualModule).isEmpty
  let mutualFormattedAgain ←
    Formatter.formatSourceWithEnv env mutualResult.formatted
      "mutual-termination-clauses-formatted-again.lean"
  assertEq "mutual termination clause alignment is idempotent"
    mutualResult.formatted mutualFormattedAgain

def assertDocumentedMutualCommandsKeepBase (env : Lean.Environment) : IO Unit := do
  let source :=
    "mutual\n"
    ++ "\n"
    ++ "theorem first : True := by\n"
    ++ "  trivial\n"
    ++ "\n"
    ++ "/-- The second theorem. -/\n"
    ++ "theorem second : True := by\n"
    ++ "  trivial\n"
    ++ "\n"
    ++ "end\n"
  let expected :=
    "mutual\n"
    ++ "\n"
    ++ "  theorem first : True := by\n"
    ++ "    trivial\n"
    ++ "\n"
    ++ "  /-- The second theorem. -/\n"
    ++ "  theorem second : True := by\n"
    ++ "    trivial\n"
    ++ "\n"
    ++ "end\n"
  let result ←
    Formatter.formatSourceWithEnvDetailed env source "documented-mutual-commands.lean"
  assertTrue "documented mutual declarations do not fall back" (!result.fellBack)
  assertEq "documented mutual declarations use the mutual body base"
    expected result.formatted
  assertTrue "documented mutual declarations preserve code"
    (← codePreservedIgnoringWhitespace env source result.formatted)
  let formattedAgain ←
    Formatter.formatSourceWithEnv env result.formatted
      "documented-mutual-commands-formatted.lean"
  assertEq "documented mutual declaration layout is idempotent"
    result.formatted formattedAgain

def assertMovedDocumentedDoLetRecRebasesCommentedArms (env : Lean.Environment)
    : IO Unit := do
  let source :=
    "def run : Nat :=\n"
    ++ "  id (Id.run do\n"
    ++ "    let rec\n"
    ++ "    /-- First helper. -/\n"
    ++ "    first : Nat → Nat\n"
    ++ "      | 0 => 0,\n"
    ++ "    /-- Second helper. -/\n"
    ++ "    second : Nat → Nat\n"
    ++ "      | 0 =>\n"
    ++ "        -- Preserve this comment.\n"
    ++ "        first 0\n"
    ++ "    pure (second 0))\n"
  let expected :=
    "def run : Nat :=\n"
    ++ "  id\n"
    ++ "    (Id.run\n"
    ++ "      do\n"
    ++ "        let rec\n"
    ++ "        /-- First helper. -/\n"
    ++ "        first : Nat → Nat\n"
    ++ "          | 0 => 0,\n"
    ++ "        /-- Second helper. -/\n"
    ++ "        second : Nat → Nat\n"
    ++ "          | 0 =>\n"
    ++ "              -- Preserve this comment.\n"
    ++ "              first 0\n"
    ++ "        pure (second 0))\n"
  let result ←
    Formatter.formatSourceWithEnvDetailed env source "moved-documented-do-let-rec.lean"
  assertTrue "moved documented do-let-rec does not fall back" (!result.fellBack)
  assertEq "moved documented do-let-rec rebases declarations and comments"
    expected result.formatted
  assertTrue "moved documented do-let-rec preserves code"
    (← codePreservedIgnoringWhitespace env source result.formatted)
  let formattedAgain ←
    Formatter.formatSourceWithEnv env result.formatted
      "moved-documented-do-let-rec-formatted.lean"
  assertEq "moved documented do-let-rec is idempotent" result.formatted formattedAgain

def assertBasicDeclarationBreak (env : Lean.Environment) : IO Unit := do
  let source :=
    "def declarationTreeBodyBreak : Nat := veryLongIdentifierNameThatPushesTheDefinitionBodyPastTheWidthLimit\n"
  let expected :=
    "def declarationTreeBodyBreak : Nat :=\n"
    ++ "  veryLongIdentifierNameThatPushesTheDefinitionBodyPastTheWidthLimit\n"
  let formatted ← Formatter.formatSourceWithEnv env source "declaration-break.lean"
  assertEq "declaration body break" expected formatted

def assertTopLevelAnnotationsBreakConsistently (env : Lean.Environment) : IO Unit := do
  let annotation :=
    "@[foo /- first line\nannotation continuation occupies most of the formatting width -/]"
  let commands :=
    [
      ("definition", "def", "def annotatedDefinition := 1\n"),
      (
        "modified definition",
        "private def",
        "private def annotatedPrivateDefinition := 1\n"
      ),
      ("theorem", "theorem", "theorem annotatedTheorem : True := by trivial\n"),
      ("axiom", "axiom", "axiom annotatedAxiom : True\n"),
      ("example", "example", "example : True := by trivial\n"),
      ("opaque", "opaque", "opaque annotatedOpaque : Nat\n"),
      ("abbreviation", "abbrev", "abbrev AnnotatedAbbreviation := Nat\n"),
      ("structure", "structure", "structure AnnotatedStructure where\n  field : Nat\n"),
      ("inductive", "inductive", "inductive AnnotatedInductive where\n  | constructor\n"),
      ("class", "class", "class AnnotatedClass where\n  field : Nat\n"),
      (
        "instance",
        "instance",
        "instance : Inhabited AnnotatedStructure where\n  default := { field := 0 }\n"
      )
    ]
  for (name, commandPrefix, command) in commands do
    let source := annotation ++ " " ++ command
    let formatted ← Formatter.formatSourceWithEnv env source s!"annotated-{name}.lean"
    assertTextContains s!"{name} starts after its overflowing annotation"
      formatted (annotation ++ "\n" ++ commandPrefix)
    let second ←
      Formatter.formatSourceWithEnv env formatted s!"annotated-{name}-second.lean"
    assertEq s!"{name} annotation break is idempotent" formatted second
    let sourceBrokenBeforeCommand := "@[simp]\n" ++ command
    let formattedBrokenBeforeCommand ←
      Formatter.formatSourceWithEnv env sourceBrokenBeforeCommand
        s!"source-broken-annotated-{name}.lean"
    assertTextContains s!"{name} preserves its source annotation break"
      formattedBrokenBeforeCommand ("@[simp]\n" ++ commandPrefix)

def assertDeclarationValueInfixBreaksAfterAssign (env : Lean.Environment) : IO Unit := do
  let source :=
    "def declarationValueInfixBreakWithLongEnoughHeaderExtra : Nat := inferInstanceAs <| OfNat Nat 0\n"
  let expected :=
    "def declarationValueInfixBreakWithLongEnoughHeaderExtra : Nat :=\n"
    ++ "  inferInstanceAs <| OfNat Nat 0\n"
  let formatted ←
    Formatter.formatSourceWithEnv env source "declaration-value-infix-break.lean"
  assertEq "declaration value infix breaks after assignment" expected formatted

def assertLongDeclarationDirectValueBreaksAfterAssign (env : Lean.Environment)
    : IO Unit := do
  let source :=
    "theorem declarationDirectValueBreaksAfterAssignWithLongEnoughName : True := veryLongDirectTheoremValueNameForLayoutTestingAndOverflow\n"
  let expected :=
    "theorem declarationDirectValueBreaksAfterAssignWithLongEnoughName : True :=\n"
    ++ "  veryLongDirectTheoremValueNameForLayoutTestingAndOverflow\n"
  let formatted ←
    Formatter.formatSourceWithEnv env source "declaration-direct-value-break.lean"
  assertEq "long declaration direct value breaks after assignment" expected formatted

def assertDeclarationProofValueBreaksAfterAssignWhenSignatureCannotFit
    (env : Lean.Environment)
    : IO Unit := do
  let theoremSource :=
    "theorem theoremProofValueBreaksAfterAssign (x : Nat) (h : x = x) : x + x + x + x + x + x + x + x + x + x = x + x + x + x + x + x + x + x + x + x := by rw [h]\n"
  let theoremExpected :=
    "theorem theoremProofValueBreaksAfterAssign (x : Nat) (h : x = x)\n"
    ++ "    : x + x + x + x + x + x + x + x + x + x = x + x + x + x + x + x + x + x + x + x := by\n"
    ++ "  rw [h]\n"
  let theoremFormatted ←
    Formatter.formatSourceWithEnv env theoremSource
      "theorem-proof-value-assignment-break.lean"
  assertEq "theorem proof value breaks after assignment when signature cannot fit"
    theoremExpected theoremFormatted
  let defSource :=
    "def definitionProofValueBreaksAfterAssign (x : Nat) : x + x + x + x + x + x + x + x + x + x = x + x + x + x + x + x + x + x + x + x := by rw [Nat.add_comm]\n"
  let defExpected :=
    "def definitionProofValueBreaksAfterAssign (x : Nat)\n"
    ++ "    : x + x + x + x + x + x + x + x + x + x = x + x + x + x + x + x + x + x + x + x := by\n"
    ++ "  rw [Nat.add_comm]\n"
  let defFormatted ←
    Formatter.formatSourceWithEnv env defSource
      "definition-proof-value-assignment-break.lean"
  assertEq "definition proof value breaks after assignment when signature cannot fit"
    defExpected defFormatted

def assertDeclarationProofIntroducerStaysWithAssignment (env : Lean.Environment)
    : IO Unit := do
  let source :=
    "theorem proofIntroducerStaysWithAssignmentAfterLongSignature (schema : Schema) (left right : Operation) (hsem : operationsSemanticallyEquivalentForCompleteBoolVars schema (operationBoolVars left) left right) : completeNormalOperationsEqualUpToReordering left right := by\n"
    ++ "  classical\n"
    ++ "  exact proof\n"
  let expected :=
    "theorem proofIntroducerStaysWithAssignmentAfterLongSignature (schema : Schema)\n"
    ++ "    (left right : Operation)\n"
    ++ "    (hsem\n"
    ++ "      : operationsSemanticallyEquivalentForCompleteBoolVars schema\n"
    ++ "          (operationBoolVars left) left right)\n"
    ++ "    : completeNormalOperationsEqualUpToReordering left right := by\n"
    ++ "  classical\n"
    ++ "  exact proof\n"
  let formatted ←
    Formatter.formatSourceWithEnv env source
      "declaration-proof-introducer-assignment.lean"
  assertEq "declaration proof introducer stays with assignment" expected formatted

def assertDeclarationValueWithNestedProofBreaksAfterAssignment (env : Lean.Environment)
    : IO Unit := do
  let source :=
    "theorem declarationValueNestedProofBreaksAfterAssignment {schema : Schema} {left : List Selection} (hleft : ExecutionStateEquivalent { window := { schema := schema, selectionSet := left }, initial := .object [] }) : ExecutionStateEquivalent { window := { schema := schema, selectionSet := left ++ [selection] }, initial := .object [] } := stateEquivalent_of_append_single_selection_noop hleft (by\n"
    ++ "      intro fields\n"
    ++ "      exact firstProof) (by\n"
    ++ "      simp [secondProof])\n"
  let expected :=
    "theorem declarationValueNestedProofBreaksAfterAssignment {schema : Schema}\n"
    ++ "    {left : List Selection}\n"
    ++ "    (hleft\n"
    ++ "      : ExecutionStateEquivalent\n"
    ++ "          { window := { schema := schema, selectionSet := left }, initial := .object [] })\n"
    ++ "    : ExecutionStateEquivalent\n"
    ++ "        {\n"
    ++ "          window := { schema := schema, selectionSet := left ++ [selection] },\n"
    ++ "          initial := .object []\n"
    ++ "        } :=\n"
    ++ "  stateEquivalent_of_append_single_selection_noop hleft (by\n"
    ++ "      intro fields\n"
    ++ "      exact firstProof) (by\n"
    ++ "      simp [secondProof])\n"
  let formatted ←
    Formatter.formatSourceWithEnv env source
      "declaration-value-nested-proof-assignment-break.lean"
  assertEq "declaration value with nested proof breaks after assignment"
    expected formatted

def assertTheoremDirectValueBreaksBeforeSignatureChildren (env : Lean.Environment)
    : IO Unit := do
  let equalitySource :=
    "theorem directValueBreaksBeforeReturnEqualityChildren {schema : Schema} {resolvers : Resolvers ObjectIdentity} (state : RecursiveGroupedOperationState schema resolvers variableValues operation depth source) : executeQueryWithFuel schema resolvers variableValues operation (depth + 1) source = GraphQL.Execution.executeQueryWithFuel schema resolvers variableValues operation (depth + 1) source := state.executeQueryWithFuel_eq_spec\n"
  let equalityExpected :=
    "theorem directValueBreaksBeforeReturnEqualityChildren {schema : Schema}\n"
    ++ "    {resolvers : Resolvers ObjectIdentity}\n"
    ++ "    (state\n"
    ++ "      : RecursiveGroupedOperationState schema resolvers variableValues operation depth\n"
    ++ "          source)\n"
    ++ "    : executeQueryWithFuel schema resolvers variableValues operation (depth + 1) source\n"
    ++ "      = GraphQL.Execution.executeQueryWithFuel schema resolvers variableValues operation\n"
    ++ "          (depth + 1) source :=\n"
    ++ "  state.executeQueryWithFuel_eq_spec\n"
  let equalityFormatted ←
    Formatter.formatSourceWithEnv env equalitySource
      "theorem-direct-value-return-equality-break.lean"
  assertEq "theorem direct value breaks before return equality children"
    equalityExpected equalityFormatted
  let constructorSource :=
    "theorem directValueBreaksBeforeReturnApplicationChildren {schema : Schema} {resolvers : Resolvers ObjectIdentity} (step : ExecutedFieldAppendStep schema resolvers variableValues depth parentType source responseName field resolved prefixTail later) (restPlan : ExecutedFieldAppendPlan schema resolvers variableValues depth parentType source responseName field resolved (prefixTail ++ [later]) rest) : ExecutedFieldAppendPlan schema resolvers variableValues depth parentType source responseName field resolved prefixTail (later :: rest) := ⟨step, restPlan⟩\n"
  let constructorExpected :=
    "theorem directValueBreaksBeforeReturnApplicationChildren {schema : Schema}\n"
    ++ "    {resolvers : Resolvers ObjectIdentity}\n"
    ++ "    (step\n"
    ++ "      : ExecutedFieldAppendStep schema resolvers variableValues depth parentType source\n"
    ++ "          responseName field resolved prefixTail later)\n"
    ++ "    (restPlan\n"
    ++ "      : ExecutedFieldAppendPlan schema resolvers variableValues depth parentType source\n"
    ++ "          responseName field resolved (prefixTail ++ [later]) rest)\n"
    ++ "    : ExecutedFieldAppendPlan schema resolvers variableValues depth parentType source\n"
    ++ "        responseName field resolved prefixTail (later :: rest) :=\n"
    ++ "  ⟨step, restPlan⟩\n"
  let constructorFormatted ←
    Formatter.formatSourceWithEnv env constructorSource
      "theorem-direct-value-return-application-break.lean"
  assertEq "theorem direct value breaks before return application children"
    constructorExpected constructorFormatted

def assertDeclarationWhereSuffixCountsForSignatureFit (env : Lean.Environment)
    : IO Unit := do
  let source :=
    "def whereSuffixSignatureFitXXXXXXXXXXXXXXXXXXXXXX (h : Function.Surjective Nat.succ) : Inhabited Nat where\n"
    ++ "  default := 0\n"
  let expected :=
    "def whereSuffixSignatureFitXXXXXXXXXXXXXXXXXXXXXX (h : Function.Surjective Nat.succ)\n"
    ++ "    : Inhabited Nat where\n"
    ++ "  default := 0\n"
  let formatted ←
    Formatter.formatSourceWithEnv env source
      "declaration-where-suffix-signature-fit.lean" { lineWidth := 100 }
  assertEq "declaration where suffix counts for signature fit" expected formatted

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

def assertAttachedDoInAssignmentInfixUsesDeclarationBase (env : Lean.Environment)
    : IO Unit := do
  let source :=
    "def isBlackListed {m} [Monad m] [MonadEnv m] (declName : Name) : m Bool := do\n"
    ++ "  if declName == ``sorryAx then return true\n"
    ++ "  let env ← getEnv\n"
    ++ "  pure <| declName.isInternalDetail || isAuxRecursor env declName || isNoConfusion env declName\n"
    ++ "  <||> isRec declName <||> isMatcher declName\n"
  let expected :=
    "def isBlackListed {m} [Monad m] [MonadEnv m] (declName : Name) : m Bool := do\n"
    ++ "  if declName == ``sorryAx then\n"
    ++ "    return true\n"
    ++ "  let env ← getEnv\n"
    ++ "  pure <| declName.isInternalDetail || isAuxRecursor env declName || isNoConfusion env declName\n"
    ++ "  <||> isRec declName\n"
    ++ "  <||> isMatcher declName\n"
  let result ←
    Formatter.formatSourceWithEnvDetailed env source
      "attached-do-in-assignment-infix.lean" { lineWidth := 100 }
  assertTrue "attached do assignment infix does not fall back" (!result.fellBack)
  assertEq "attached do assignment infix uses declaration base" expected result.formatted
  assertTrue "attached do assignment infix preserves code"
    (← codePreservedIgnoringWhitespace env source result.formatted)
  let formattedAgain ←
    Formatter.formatSourceWithEnv env result.formatted
      "attached-do-in-assignment-infix-formatted.lean" { lineWidth := 100 }
  assertEq "attached do assignment infix is idempotent" result.formatted formattedAgain

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
  assertEq "direct proof value layout is idempotent" directFormatted directFormattedAgain
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
    ++ "    : ProjectivePlane (ProjectivePoint K (Fin 3 → K)) (ProjectiveLine K (Fin 3 → K)) :=\n"
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

def assertOriginalLayoutValueHonorsDeclarationBreak (env : Lean.Environment)
    : IO Unit := do
  let source :=
    "theorem Semigroup.mem_center_iff {z : M} : z ∈ Set.center M ↔ ∀ g, g * z = z * g := ⟨fun a g ↦ by rw [IsMulCentral.comm a g],\n"
    ++ "  fun h ↦ ⟨fun _ ↦ (h _).symm, fun _ _ ↦ (mul_assoc z _ _).symm, fun _ _ ↦ mul_assoc _ _ z⟩ ⟩\n"
  let formatted ←
    Formatter.formatSourceWithEnv env source "original-layout-value-break.lean"
      { lineWidth := 100 }
  assertTrue "original-layout declaration value preserves code"
    (← codePreservedIgnoringWhitespace env source formatted)
  assertTextContains "original-layout declaration value honors assignment break"
    formatted ":=\n  ⟨fun"
  assertTextLacks "original-layout declaration value does not erase assignment break"
    formatted ":= ⟨fun"
  let formattedAgain ←
    Formatter.formatSourceWithEnv env formatted
      "original-layout-value-break-formatted.lean" { lineWidth := 100 }
  assertEq "original-layout declaration value formatting is idempotent"
    formatted formattedAgain

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

def assertHaveTermFormatting (env : Lean.Environment) : IO Unit := do
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
    Formatter.formatSourceWithEnvDetailed env source "have-term-formatting.lean"
  assertTrue "have term layout does not fall back" (!result.fellBack)
  assertEq "short have term layout remains compact" expected result.formatted
  let _ ←
    SyntaxTree.parseModuleStringWithEnv env result.formatted
      "have-term-formatting-formatted.lean"
  let formattedAgain ←
    Formatter.formatSourceWithEnv env result.formatted
      "have-term-formatting-formatted.lean"
  assertEq "have term layout is idempotent" result.formatted formattedAgain
  let longSource :=
    "def sample : Result :=\n"
    ++ "  (have : VeryLongTypeName firstArgument secondArgument thirdArgument := veryLongValueName firstArgument secondArgument thirdArgument\n"
    ++ "   useProof this)\n"
  let longExpected :=
    "def sample : Result :=\n"
    ++ "  (have : VeryLongTypeName firstArgument secondArgument thirdArgument :=\n"
    ++ "    veryLongValueName firstArgument secondArgument thirdArgument\n"
    ++ "  useProof this)\n"
  let longResult ←
    Formatter.formatSourceWithEnvDetailed env longSource "long-have-term-formatting.lean"
  assertTrue "long have term formatting does not fall back" (!longResult.fellBack)
  assertEq "long have binding breaks after assignment" longExpected longResult.formatted
  let longFormattedAgain ←
    Formatter.formatSourceWithEnv env longResult.formatted
      "long-have-term-formatting-formatted.lean"
  assertEq "long have term formatting is idempotent"
    longResult.formatted longFormattedAgain
  let dependentReturnSource :=
    "def dependentHaveReturnTypeWithEnoughHeaderCharactersToRequireSignatureWrapping :\n"
    ++ "    have : Left = Right := by\n"
    ++ "      exact proof\n"
    ++ "    Result this :=\n"
    ++ "  result\n"
  let dependentReturnExpected :=
    "def dependentHaveReturnTypeWithEnoughHeaderCharactersToRequireSignatureWrapping\n"
    ++ "    : have : Left = Right := by\n"
    ++ "        exact proof\n"
    ++ "      Result this :=\n"
    ++ "  result\n"
  let dependentReturnResult ←
    Formatter.formatSourceWithEnvDetailed env dependentReturnSource
      "dependent-have-return-type.lean" { lineWidth := 100 }
  assertTrue "dependent have return type does not fall back"
    (!dependentReturnResult.fellBack)
  assertEq "dependent have return type keeps proof and body offside"
    dependentReturnExpected dependentReturnResult.formatted
  assertTrue "dependent have return type preserves code"
    (← codePreservedIgnoringWhitespace
        env dependentReturnSource dependentReturnResult.formatted)
  let dependentReturnAgain ←
    Formatter.formatSourceWithEnv env dependentReturnResult.formatted
      "dependent-have-return-type-formatted.lean" { lineWidth := 100 }
  assertEq "dependent have return type is idempotent"
    dependentReturnResult.formatted dependentReturnAgain

def assertHaveProofAfterInfixPreservesLayout (env : Lean.Environment) : IO Unit := do
  let source :=
    "def f (hM : ∃ n : Nat, n = n) : Nat :=\n"
    ++ "  id <|\n"
    ++ "  have hex : ∃ n : Nat, n = n := by\n"
    ++ "    obtain ⟨n, h⟩ := hM; refine ⟨n, h⟩\n"
    ++ "  Nat.succ (Classical.choose hex)\n"
  let expected :=
    "def f (hM : ∃ n : Nat, n = n) : Nat :=\n"
    ++ "  id\n"
    ++ "  <|\n"
    ++ "  have hex : ∃ n : Nat, n = n := by\n"
    ++ "    obtain ⟨n, h⟩ := hM; refine ⟨n, h⟩\n"
    ++ "  Nat.succ (Classical.choose hex)\n"
  let formatted ← Formatter.formatSourceWithEnv env source "have-proof-after-infix.lean"
  assertEq "have proof after infix keeps the proof offside" expected formatted
  assertTrue "have proof after infix preserves code"
    (← codePreservedIgnoringWhitespace env source formatted)
  let formattedAgain ←
    Formatter.formatSourceWithEnv env formatted "have-proof-after-infix-formatted.lean"
  assertEq "have proof after infix is idempotent" formatted formattedAgain

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

def assertSymmetricDelimitersStayAttachedAcrossPasses (env : Lean.Environment)
    : IO Unit := do
  let source :=
    "notation \"‖\" x \"‖\" => x\n\n"
    ++ "theorem symmetricDelimiterSignatureWraps\n"
    ++ "    (h : VeryLongHypothesisNameForSymmetricDelimiterLayoutTesting) :\n"
    ++ "    ‖firstVeryLongExpressionForSymmetricDelimiterFormatting -\n"
    ++ "      (secondVeryLongExpressionForSymmetricDelimiterFormatting -\n"
    ++ "        thirdVeryLongExpressionForSymmetricDelimiterFormatting)‖ ≤\n"
    ++ "      2 * epsilon * veryLongBoundForSymmetricDelimiterFormatting := by\n"
    ++ "  -- Keep this comment attached to the proof.\n"
    ++ "  exact proof\n"
  let result ←
    Formatter.formatSourceWithEnvDetailed env source "symmetric-delimiters.lean"
      { lineWidth := 100 }
  assertTrue "symmetric delimiters do not trigger fallback" (!result.fellBack)
  assertTextLacks "symmetric delimiter closing token keeps its expression base"
    result.formatted "\n‖"
  assertTextLacks "symmetric delimiter relation keeps its signature base"
    result.formatted "\n≤"
  assertTextContains "proof comment keeps its proof-body base"
    result.formatted "\n  -- Keep this comment attached to the proof.\n"
  let formattedAgain ←
    Formatter.formatSourceWithEnv env result.formatted
      "symmetric-delimiters-formatted.lean" { lineWidth := 100 }
  assertEq "symmetric delimiter formatting is idempotent" result.formatted formattedAgain

def assertGeneratedPostfixMarkersStayAttached (env : Lean.Environment) : IO Unit := do
  let source :=
    "namespace Matrix\n\n"
    ++ "postfix:max \"ᵀ\" => id\n\n"
    ++ "theorem generatedPostfixMarkerStaysAttached\n"
    ++ "    : ((veryLongHeadForGeneratedPostfixMarker firstArgument secondArgument).toMatrix\n"
    ++ "          (veryLongArgumentForGeneratedPostfixMarker thirdArgument fourthArgument))ᵀ =\n"
    ++ "      expected := by\n"
    ++ "  exact proof\n\n"
    ++ "end Matrix\n"
  let result ←
    Formatter.formatSourceWithEnvDetailed env source "generated-postfix-marker.lean"
      { lineWidth := 100 }
  assertTrue "generated postfix marker does not change code" (!result.fellBack)
  assertTextLacks "generated postfix marker stays attached" result.formatted "\n        ᵀ"
  let formattedAgain ←
    Formatter.formatSourceWithEnv env result.formatted
      "generated-postfix-marker-formatted.lean" { lineWidth := 100 }
  assertEq "generated postfix marker formatting is idempotent"
    result.formatted formattedAgain

  let percentSource :=
    "syntax \"fast_instance%\" term : term\n"
    ++ "\n"
    ++ "def generatedPercentPostfixMarkerStaysAttached\n"
    ++ "    : LinearOrder (Lex (NonemptyInterval α)) :=\n"
    ++ "  fast_instance% { LinearOrder.lift' veryLongFunctionNameForPostfixMarkerLayout with\n"
    ++ "    toDecidableEq := inferInstance\n"
    ++ "    toDecidableLT := inferInstance\n"
    ++ "    toDecidableLE := inferInstance }\n"
  let percentResult ←
    Formatter.formatSourceWithEnvDetailed env percentSource
      "generated-percent-postfix-marker.lean" { lineWidth := 100 }
  assertTrue "generated percent postfix marker does not change code"
    (!percentResult.fellBack)
  assertTextContains "generated percent postfix marker stays attached"
    percentResult.formatted "fast_instance%"
  assertTextLacks "generated percent postfix marker is not split"
    percentResult.formatted "fast_instance\n"
  let percentFormattedAgain ←
    Formatter.formatSourceWithEnv env percentResult.formatted
      "generated-percent-postfix-marker-formatted.lean" { lineWidth := 100 }
  assertEq "generated percent postfix marker formatting is idempotent"
    percentResult.formatted percentFormattedAgain

  let parenthesizedSource :=
    "syntax \"q\" \"(\" term \")\" : term\n"
    ++ "\n"
    ++ "def generatedParenthesizedPostfixMarkerStaysAttached :=\n"
    ++ "  return .done <| mkSetLiteralQ q(VeryLongTypeConstructorName alphaArgument betaArgument) <| remainingValue\n"
  let parenthesizedResult ←
    Formatter.formatSourceWithEnvDetailed env parenthesizedSource
      "generated-parenthesized-postfix-marker.lean"
  assertTrue "generated parenthesized postfix marker does not change code"
    (!parenthesizedResult.fellBack)
  assertTextContains "generated parenthesized postfix marker stays attached"
    parenthesizedResult.formatted "q("
  assertTextLacks "generated parenthesized postfix marker is not split"
    parenthesizedResult.formatted "q\n"
  let parenthesizedFormattedAgain ←
    Formatter.formatSourceWithEnv env parenthesizedResult.formatted
      "generated-parenthesized-postfix-marker-formatted.lean"
  assertEq "generated parenthesized postfix marker formatting is idempotent"
    parenthesizedResult.formatted parenthesizedFormattedAgain

def assertNotExistsIdentifiersFlow (env : Lean.Environment) : IO Unit := do
  let source :=
    "assert_not_exists FirstLongDeclarationName SecondLongDeclarationName ThirdLongDeclarationName FourthLongDeclarationName FifthLongDeclarationName\n"
  let result ←
    Formatter.formatSourceWithEnvDetailed env source "assert-not-exists-identifiers.lean"
      { lineWidth := 100 }
  assertTrue "assert_not_exists formatting does not fall back" (!result.fellBack)
  assertTextContains "assert_not_exists identifiers start on a continuation line"
    result.formatted "assert_not_exists\n  FirstLongDeclarationName"
  let moduleTree ←
    SyntaxTree.parseModuleStringWithEnv env result.formatted
      "assert-not-exists-identifiers-formatted.lean"
  assertTrue "assert_not_exists identifiers fit the configured width"
    (Formatter.Diagnostics.overflowOccurrences moduleTree { lineWidth := 100 }).isEmpty
  let formattedAgain ←
    Formatter.formatSourceWithEnv env result.formatted
      "assert-not-exists-identifiers-formatted.lean" { lineWidth := 100 }
  assertEq "assert_not_exists identifier formatting is idempotent"
    result.formatted formattedAgain

def assertSignatureParametersUseLeadingSourceBreakAfterFlatFails (env : Lean.Environment)
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
  let formatted ← Formatter.formatSourceWithEnv env source "definition-source-assign.lean"
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
    Formatter.formatSourceWithEnv env destructuringLet "destructuring-let-assignment.lean"
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
  assertEq "let keyword stays with declaration header" typedLetExpected typedLetFormatted

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
    Formatter.formatSourceWithEnv env monadicTupleLet "monadic-tuple-let-assignment.lean"
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
    ++ "  | fieldSelection@(.field _responseName fieldName _arguments _directives veryLongSelectionSet)\n"
    ++ "    =>\n"
    ++ "      Validation.selectionValid schema variableDefinitions parentType fieldSelection\n"
  let longAliasPatternExpected :=
    "def operatorLedMatchConjunction (schema : Schema)\n"
    ++ "    (variableDefinitions : List VariableDefinition)\n"
    ++ "    (parentType : Name)\n"
    ++ "    : Selection -> Prop\n"
    ++ "  | fieldSelection@(\n"
    ++ "        .field _responseName fieldName _arguments _directives veryLongSelectionSet) =>\n"
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
    ++ "  if !isFlow && !(sourceBreaksAllowedByBreakPointsInCurrentState state segment breakPoints).isEmpty then\n"
    ++ "    first\n"
    ++ "  else\n"
    ++ "    second\n"
  let bangConjunctionExpected :=
    "def choose isFlow state segment breakPoints :=\n"
    ++ "  if !isFlow\n"
    ++ "      && !(sourceBreaksAllowedByBreakPointsInCurrentState state segment\n"
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
    ++ "  veryLongFunctionNameForTreeFormatting firstArgumentNameForTree secondArgumentNameForTree\n"
    ++ "    thirdArgumentNameForTree\n"
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

def assertApplicationCommentBreakAvoidsOverflowAfterOuterShift (env : Lean.Environment)
    : IO Unit := do
  let source :=
    "def sourceBrokenCommentArgument :=\n"
    ++ "  wrapper fun cmd => do\n"
    ++ "    unless condition do\n"
    ++ "      return\n"
    ++ "    cmd.apply\n"
    ++ "      /- Keep this explanation with the named argument. -/\n"
    ++ "      (option := value)\n"
    ++ "      predicate\n"
    ++ "      fun x => do\n"
    ++ "        consume x\n"
  let expected :=
    "def sourceBrokenCommentArgument :=\n"
    ++ "  wrapper\n"
    ++ "    fun cmd =>\n"
    ++ "      do\n"
    ++ "        unless condition do\n"
    ++ "          return\n"
    ++ "        cmd.apply\n"
    ++ "        /- Keep this explanation with the named argument. -/\n"
    ++ "          (option := value)\n"
    ++ "          predicate\n"
    ++ "          fun x =>\n"
    ++ "            do\n"
    ++ "              consume x\n"
  let formatted ←
    Formatter.formatSourceWithEnv env source
      "application-comment-source-break.lean" { lineWidth := 60 }
  assertEq "application comment source break avoids overflow after outer shift"
    expected formatted
  assertTrue "application comment source break stays within the configured width"
    (Formatter.linesFit formatted 60)
  assertTrue "shifted application comment source break preserves code"
    (← codePreservedIgnoringWhitespace env source formatted)
  let formattedAgain ←
    Formatter.formatSourceWithEnv env formatted
      "application-comment-source-break-formatted.lean" { lineWidth := 60 }
  assertEq "shifted application comment source break is idempotent"
    formatted formattedAgain

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
  let source := "def letBodyBreak : Result :=\n" ++ "  let value := f a\n" ++ "  value\n"
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
    "def letBodyBlocksFlat : Prop :=\n" ++ "  let first := value\n" ++ "  Result first\n"
  let formatted ← Formatter.formatSourceWithEnv env source "let-flat-rendering.lean"
  assertEq "let expression blocks flat rendering" expected formatted

def assertParenthesizedLetIKeepsTightOpeningDelimiter (env : Lean.Environment)
    : IO Unit := do
  let source :=
    "def parenthesizedLetI (m₁ m₂ : Nat) : Prop := (letI := m₁; HMul.hMul : M → M → M) = (letI := m₂; HMul.hMul : M → M → M)\n"
  let formatted ←
    Formatter.formatSourceWithEnv env source "parenthesized-letI-tight-opening.lean"
  assertTrue "parenthesized letI preserves code"
    (← codePreservedIgnoringWhitespace env source formatted)
  assertTextContains "parenthesized letI stays attached to opening delimiter"
    formatted "(letI"
  assertTextLacks "parenthesized letI does not gain alignment padding" formatted "( letI"
  let formattedAgain ←
    Formatter.formatSourceWithEnv env formatted
      "parenthesized-letI-tight-opening-formatted.lean"
  assertEq "parenthesized letI formatting is idempotent" formatted formattedAgain

def assertBinderLetIDoesNotPadAfterColon (env : Lean.Environment) : IO Unit := do
  let source :=
    "def binderLetI [h : letI := veryLongInstanceProviderName alphaArgument functionArgument; VeryLongTypeclassName alphaArgument] : Nat := default\n"
  let formatted ← Formatter.formatSourceWithEnv env source "binder-letI-spacing.lean"
  assertTrue "binder letI preserves code"
    (← codePreservedIgnoringWhitespace env source formatted)
  assertTextContains "binder letI uses one space after colon" formatted ": letI"
  assertTextLacks "binder letI does not add alignment padding" formatted ":  letI"
  let formattedAgain ←
    Formatter.formatSourceWithEnv env formatted "binder-letI-spacing-formatted.lean"
  assertEq "binder letI formatting is idempotent" formatted formattedAgain

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
  let applicationSource :=
    "theorem parenthesizedLetBody (h : Hypothesis) : Result :=\n"
    ++ "  let ⟨i, hi⟩ := h\n"
    ++ "  total.elim id fun hgf =>\n"
    ++ "    False.elim\n"
    ++ "      (let ⟨K, hK0, j, hKj⟩ := hgf\n"
    ++ "      contradiction hi K hK0 j hKj)\n"
  let applicationExpected :=
    "theorem parenthesizedLetBody (h : Hypothesis) : Result :=\n"
    ++ "  let ⟨i, hi⟩ := h\n"
    ++ "  total.elim id\n"
    ++ "    fun hgf =>\n"
    ++ "      False.elim\n"
    ++ "        ( let ⟨K, hK0, j, hKj⟩ := hgf\n"
    ++ "          contradiction hi K hK0 j hKj)\n"
  let applicationFormatted ←
    Formatter.formatSourceWithEnv env applicationSource
      "parenthesized-let-body-in-application.lean" { lineWidth := 100 }
  assertEq "parenthesized let body closes at its containing indentation"
    applicationExpected applicationFormatted
  assertTrue "parenthesized let body preserves syntax"
    (← codePreservedIgnoringWhitespace env applicationSource applicationFormatted)

def assertParenthesizedLetAlignmentFollowsBodyPrecedence (env : Lean.Environment)
    : IO Unit := do
  let source :=
    "def offColumnIdentifierLet : Prop :=\n"
    ++ "  normalizedSubselections\n"
    ++ "  = (let matching := veryLongFieldSelectionsWithResponseNameInScope schema parentType responseName rest\n"
    ++ "      let merged := mergeSelectionSets matching\n"
    ++ "      predicate merged)\n"
    ++ "\n"
    ++ "def offColumnPatternLet : Prop :=\n"
    ++ "  normalizedSubselections\n"
    ++ "  = (let (matching, errors) := veryLongFieldSelectionsWithErrorsInScope schema parentType responseName rest; predicate matching errors)\n"
  let expected :=
    "def offColumnIdentifierLet : Prop :=\n"
    ++ "  normalizedSubselections\n"
    ++ "  = (let matching :=\n"
    ++ "        veryLongFieldSelectionsWithResponseNameInScope schema parentType responseName rest\n"
    ++ "      let merged := mergeSelectionSets matching\n"
    ++ "      predicate merged)\n"
    ++ "\n"
    ++ "def offColumnPatternLet : Prop :=\n"
    ++ "  normalizedSubselections\n"
    ++ "  = (let (matching, errors) :=\n"
    ++ "        veryLongFieldSelectionsWithErrorsInScope schema parentType responseName rest;\n"
    ++ "      predicate matching errors)\n"
  let formatted ←
    Formatter.formatSourceWithEnv env source "off-column-parenthesized-let-rhs.lean"
  assertEq "parenthesized let alignment follows body precedence" expected formatted
  assertTrue "off-column parenthesized let preserves code"
    (← codePreservedIgnoringWhitespace env source formatted)

def assertParenthesizedLetWithMatchBodyKeepsTightOpening (env : Lean.Environment)
    : IO Unit := do
  let source :=
    "def parenthesizedLetMatchBody : Prop :=\n"
    ++ "  staticCollectForGround schema variables lookupParent groundType boolCase rest\n"
    ++ "  = ( let collectedRest :=\n"
    ++ "        staticCollectForGroundWithEnoughCharactersForLayoutTesting\n"
    ++ "          schema variables lookupParent groundType\n"
    ++ "          boolCase rest\n"
    ++ "      match schema.lookupField lookupParent fieldName with\n"
    ++ "      | none => collectedRest\n"
    ++ "      | some fieldDefinition => collectedRest)\n"
  let expected :=
    "def parenthesizedLetMatchBody : Prop :=\n"
    ++ "  staticCollectForGround schema variables lookupParent groundType boolCase rest\n"
    ++ "  = (let collectedRest :=\n"
    ++ "        staticCollectForGroundWithEnoughCharactersForLayoutTesting\n"
    ++ "          schema variables lookupParent groundType\n"
    ++ "          boolCase rest\n"
    ++ "      match schema.lookupField lookupParent fieldName with\n"
    ++ "      | none => collectedRest\n"
    ++ "      | some fieldDefinition => collectedRest)\n"
  let formatted ←
    Formatter.formatSourceWithEnv env source "parenthesized-let-match-body.lean"
  assertEq "parenthesized let with match body keeps tight opening" expected formatted
  assertTrue "parenthesized let with match body preserves code"
    (← codePreservedIgnoringWhitespace env source formatted)
  let formattedAgain ←
    Formatter.formatSourceWithEnv env formatted
      "parenthesized-let-match-body-formatted.lean"
  assertEq "parenthesized let with match body formatting is idempotent"
    formatted formattedAgain

def assertParenthesizedLetUsesProjectSyntaxPrecedence (env : Lean.Environment)
    : IO Unit := do
  let source :=
    "syntax:lead \"project_leading_body\" : term\n"
    ++ "syntax:max \"project_argument_body\" : term\n"
    ++ "\n"
    ++ "def leadingSyntaxLet : Prop :=\n"
    ++ "  result = (let value := exceptionallyLongValueProviderNameForLayoutTesting argument\n"
    ++ "    project_leading_body)\n"
    ++ "\n"
    ++ "def argumentSyntaxLet : Prop :=\n"
    ++ "  result = (let value := exceptionallyLongValueProviderNameForLayoutTesting argument\n"
    ++ "    project_argument_body)\n"
  let formatted ←
    Formatter.formatSourceWithEnv env source "let-project-syntax-precedence.lean"
  assertTextContains "leading project syntax keeps tight let opening"
    formatted "= (let value :="
  assertTextContains "argument project syntax aligns let opening"
    formatted "= ( let value :="
  assertTrue "project syntax let formatting preserves code"
    (← codePreservedIgnoringWhitespace env source formatted)
  let formattedAgain ←
    Formatter.formatSourceWithEnv env formatted
      "let-project-syntax-precedence-formatted.lean"
  assertEq "project syntax let formatting is idempotent" formatted formattedAgain

def assertTheoremParenthesizedLetKeepsValueSuffix (env : Lean.Environment) : IO Unit := do
  let source :=
    "theorem repeatedSiblingSelectionsUseSingleFragmentSmoke\n"
    ++ "    : ( let minimized :=\n"
    ++ "          GraphQL.NamedFragment.Minimize.minimize\n"
    ++ "            Execution.sampleSchema repeatedSiblingSelectionSetOperation\n"
    ++ "        minimized.fragmentDefinitions.length = 1) := by\n"
    ++ "  native_decide\n"
  let expected :=
    "theorem repeatedSiblingSelectionsUseSingleFragmentSmoke\n"
    ++ "    : ( let minimized :=\n"
    ++ "          GraphQL.NamedFragment.Minimize.minimize\n"
    ++ "            Execution.sampleSchema repeatedSiblingSelectionSetOperation\n"
    ++ "        minimized.fragmentDefinitions.length = 1) := by\n"
    ++ "  native_decide\n"
  let formatted ←
    Formatter.formatSourceWithEnv env source "theorem-parenthesized-let-value-suffix.lean"
  assertEq "theorem parenthesized let keeps value suffix" expected formatted
  assertTrue "theorem parenthesized let preserves code"
    (← codePreservedIgnoringWhitespace env source formatted)
  let formattedAgain ←
    Formatter.formatSourceWithEnv env formatted
      "theorem-parenthesized-let-value-suffix-formatted.lean"
  assertEq "theorem parenthesized let formatting is idempotent" formatted formattedAgain

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
    Formatter.formatSourceWithEnv env source "let-body-after-infix-closes-let-layout.lean"
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
  let formatted ← Formatter.formatSourceWithEnv env source "signature-parameters-fit.lean"
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

def assertVariableInstanceBinderAvoidsBracketOnlyLines (env : Lean.Environment)
    : IO Unit := do
  let source :=
    "variable [∀ {X Y : Cᵒᵖ} (f : X ⟶ Y), PreservesColimit (F ⋙ evaluation R Y) (ModuleCat.restrictScalars (R.map f).hom)]\n"
  let formatted ←
    Formatter.formatSourceWithEnv env source "variable-instance-binder-brackets.lean"
  assertTextLacks "variable instance binder avoids newline after opening bracket"
    formatted "[\n"
  assertTextLacks "variable instance binder avoids newline before closing bracket"
    formatted "\n]"

def assertCommandBinderSequencesFlow (env : Lean.Environment) : IO Unit := do
  let source :=
    "variable {C : Type} [Add C] [Sub C] [Mul C] [Div C] [Pow C Nat]\n"
    ++ "omit [Add C] [Sub C] [Mul C] [Div C] [Pow C Nat] [LT C] [LE C] [BEq C] [Hashable C] [Inhabited C] [EmptyCollection C] in\n"
    ++ "theorem value : True := by trivial\n"
    ++ "include firstVeryLongVariableName secondVeryLongVariableName thirdVeryLongVariableName fourthVeryLongVariableName fifthVeryLongVariableName in\n"
    ++ "theorem includedValue : True := by trivial\n"
  let expected :=
    "variable {C : Type} [Add C] [Sub C] [Mul C] [Div C] [Pow C Nat]\n"
    ++ "omit\n"
    ++ "  [Add C] [Sub C] [Mul C] [Div C] [Pow C Nat] [LT C] [LE C] [BEq C] [Hashable C]\n"
    ++ "    [Inhabited C] [EmptyCollection C] in\n"
    ++ "theorem value : True := by trivial\n"
    ++ "include\n"
    ++ "  firstVeryLongVariableName secondVeryLongVariableName thirdVeryLongVariableName\n"
    ++ "    fourthVeryLongVariableName fifthVeryLongVariableName in\n"
    ++ "theorem includedValue : True := by trivial\n"
  let formatted ← Formatter.formatSourceWithEnv env source "command-binder-flow.lean"
  assertEq "command binder sequences flow between binders" expected formatted

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
  let formatted ← Formatter.formatSourceWithEnv env source "return-type-infix-indent.lean"
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
  let formatted ← Formatter.formatSourceWithEnv env source "child-fit-parent-suffix.lean"
  assertEq "child fit counts parent suffix" expected formatted

def assertNestedChildFitCountsInfixSuffix (env : Lean.Environment) : IO Unit := do
  let source :=
    "def nestedInfixSuffixExample :=\n"
    ++ "  Submodule.liftQSpanSingleton _\n"
    ++ "    (CharacterModule.int.divByNat <| if addOrderOf a = 0 then 2 else addOrderOf a).toIntLinearMap <| by\n"
    ++ "      exact h\n"
  let expected :=
    "def nestedInfixSuffixExample :=\n"
    ++ "  Submodule.liftQSpanSingleton _\n"
    ++ "    (CharacterModule.int.divByNat\n"
    ++ "      <| if addOrderOf a = 0 then 2 else addOrderOf a).toIntLinearMap <| by\n"
    ++ "      exact h\n"
  let formatted ←
    Formatter.formatSourceWithEnv env source "nested-child-fit-infix-suffix.lean"
      { lineWidth := 100 }
  assertEq "nested child fit counts an enclosing infix suffix" expected formatted

def assertNestedChildFitCountsProjectionMemberSuffix (env : Lean.Environment)
    : IO Unit := do
  let source :=
    "theorem continuousAlternatingMapCoordChange_apply\n"
    ++ "    : continuousAlternatingMapCoordChange 𝕜 ι e₁ e₁' e₂ e₂' b L\n"
    ++ "      = (continuousAlternatingMap 𝕜 ι e₁' e₂' ⟨b, (continuousAlternatingMap 𝕜 ι e₁ e₂).symm b L⟩).2 := by\n"
    ++ "  exact proof\n"
  let expected :=
    "theorem continuousAlternatingMapCoordChange_apply\n"
    ++ "    : continuousAlternatingMapCoordChange 𝕜 ι e₁ e₁' e₂ e₂' b L\n"
    ++ "      = (continuousAlternatingMap 𝕜 ι e₁' e₂'\n"
    ++ "          ⟨b, (continuousAlternatingMap 𝕜 ι e₁ e₂).symm b L⟩).2 := by\n"
    ++ "  exact proof\n"
  let result ←
    Formatter.formatSourceWithEnvDetailed env source
      "nested-child-fit-projection-member-suffix.lean" { lineWidth := 100 }
  assertTrue "projection-member suffix fit does not fall back" (!result.fellBack)
  assertEq "nested child fit counts a projection member and declaration suffix"
    expected result.formatted
  assertTrue "projection-member suffix fit preserves code"
    (← codePreservedIgnoringWhitespace env source result.formatted)
  let formattedAgain ←
    Formatter.formatSourceWithEnv env result.formatted
      "nested-child-fit-projection-member-suffix-formatted.lean" { lineWidth := 100 }
  assertEq "projection-member suffix fit is idempotent" result.formatted formattedAgain

def assertLineFitCountsTrailingComment (env : Lean.Environment) : IO Unit := do
  let source :=
    "inductive Relation : Nat → Nat → Prop\n"
    ++ "  | trans : ∀ (x y z) (_ : Relation x y) (_ : Relation y z), Relation x z -- The following constructor starts a new case\n"
    ++ "  | refl : ∀ x, Relation x x\n"
  let expected :=
    "inductive Relation : Nat → Nat → Prop\n"
    ++ "  | trans\n"
    ++ "    : ∀ (x y z) (_ : Relation x y) (_ : Relation y z),\n"
    ++ "        Relation x z -- The following constructor starts a new case\n"
    ++ "  | refl : ∀ x, Relation x x\n"
  let formatted ←
    Formatter.formatSourceWithEnv env source "line-fit-trailing-comment.lean"
  assertEq "line fit counts a comment before the next rule boundary" expected formatted
  let formattedAgain ←
    Formatter.formatSourceWithEnv env formatted "line-fit-trailing-comment.lean"
  assertEq "trailing-comment fit is idempotent" formatted formattedAgain

def assertColumnIndentationIsConservative : IO Unit := do
  assertTrue "column 3 needs only one indentation level"
    (Formatter.indentationLevelForColumn 3 == 1)
  assertTrue "column 3 rounds forward to the next indentation level"
    (Formatter.indentationPastColumn 3 == 4)
  assertTrue "ordinary breaks indent from their rounded base"
    (Formatter.breakIndent 3 2 { index := 0, indentLevels := 1 } == 6)

def assertCurrentLineFitChecksCompletedLines : IO Unit := do
  let state : Formatter.RenderState :=
    { source := "", currentLine := "12345", options := { lineWidth := 10 } }
  assertTrue "line fit rejects an introduced completed-line overflow"
    (!Formatter.currentLineFitsWith state "678901\nx")
  let alreadyOverflowing : Formatter.RenderState :=
    {
      source := ""
      currentLine := "12345678901"
      options := { lineWidth := 10 }
    }
  assertTrue "line fit ignores an untouched pre-existing completed-line overflow"
    (Formatter.currentLineFitsWith alreadyOverflowing "\nx")

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

def assertMovedProofWidgetsJsxUsesPendingIndent : IO Unit := do
  let source := "previous\n      <div>\n        child\n      </div>"
  let previous := tokenAt "previous" (String.Pos.Raw.mk 0) (String.Pos.Raw.mk 8)
  let openTag := tokenAt "<div>" (String.Pos.Raw.mk 15) (String.Pos.Raw.mk 20)
  let closeTag := tokenAt "</div>" (String.Pos.Raw.mk 41) (String.Pos.Raw.mk 47)
  let jsx :=
    SyntaxTree.Tree.node
      (.raw `ProofWidgets.Jsx.syntheticElementForIndentTest)
      #[.leaf openTag, .leaf closeTag]
  let parent := SyntaxTree.Tree.node .application #[.leaf previous, jsx]
  let state : Formatter.RenderState :=
    {
      source
      output := "previous"
      currentLine := "previous"
      lastToken? := some previous
      pendingIndent? := some 20
    }
  let rendered :=
    Formatter.renderNestedSegment state
      (Formatter.LineBreakRules.Segment.ofTree parent) 1 jsx
  let expected :=
    "previous\n"
    ++ "                    <div>\n"
    ++ "                      child\n"
    ++ "                    </div>"
  assertEq "moved original layout follows the formatter-selected indentation"
    expected rendered.output
  let payload := String.ofList (List.replicate 70 'x')
  let wideSource := "previous\n      <div>" ++ payload ++ "</div>"
  let wideOpenTag := tokenAt "<div>" (String.Pos.Raw.mk 15) (String.Pos.Raw.mk 20)
  let widePayload := tokenAt payload (String.Pos.Raw.mk 20) (String.Pos.Raw.mk 90)
  let wideCloseTag := tokenAt "</div>" (String.Pos.Raw.mk 90) (String.Pos.Raw.mk 96)
  let wideJsx :=
    SyntaxTree.Tree.node
      (.raw `ProofWidgets.Jsx.syntheticElementForIndentTest)
      #[.leaf wideOpenTag, .leaf widePayload, .leaf wideCloseTag]
  let wideParent := SyntaxTree.Tree.node .application #[.leaf previous, wideJsx]
  let wideState : Formatter.RenderState :=
    {
      source := wideSource
      output := "previous"
      currentLine := "previous"
      lastToken? := some previous
      pendingIndent? := some 20
      options := { lineWidth := 100 }
    }
  let wideRendered :=
    Formatter.renderNestedSegment wideState
      (Formatter.LineBreakRules.Segment.ofTree wideParent) 1 wideJsx
  assertEq "moved JSX retains its fitting parent-relative indentation"
    wideSource wideRendered.output
  assertTrue "parent-relative JSX layout avoids introduced overflow"
    (Formatter.linesFit wideRendered.output 100)

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

def assertListLikeCollectionsBreakBalanced (env : Lean.Environment) : IO Unit := do
  let listSource :=
    "def doLetElseBreaks (_context : RuleContext) (segment : Segment) : List BreakPoint :=\n"
    ++ "  let continuationBreak := do\n"
    ++ "    let pipeIndex ← segment.indexes.find? fun index => childStartsWithLexeme segment index \"|\"\n"
    ++ "    let fallbackIndex ← (nonemptyChildIndexes segment).find? fun index => pipeIndex < index\n"
    ++ "    let continuationIndex ← (nonemptyChildIndexes segment).find? fun index => fallbackIndex < index\n"
    ++ "    boundaryBreak? segment continuationIndex 0\n"
    ++ "  [breakAfterLexeme? segment \":=\" 1, breakBeforeLexeme? segment \"|\" 0, continuationBreak].filterMap id\n"
  let listExpected :=
    "def doLetElseBreaks (_context : RuleContext) (segment : Segment) : List BreakPoint :=\n"
    ++ "  let continuationBreak := do\n"
    ++ "    let pipeIndex ←\n"
    ++ "      segment.indexes.find? fun index => childStartsWithLexeme segment index \"|\"\n"
    ++ "    let fallbackIndex ←\n"
    ++ "      (nonemptyChildIndexes segment).find? fun index => pipeIndex < index\n"
    ++ "    let continuationIndex ←\n"
    ++ "      (nonemptyChildIndexes segment).find? fun index => fallbackIndex < index\n"
    ++ "    boundaryBreak? segment continuationIndex 0\n"
    ++ "  [\n"
    ++ "    breakAfterLexeme? segment \":=\" 1,\n"
    ++ "    breakBeforeLexeme? segment \"|\" 0,\n"
    ++ "    continuationBreak\n"
    ++ "  ].filterMap\n"
    ++ "    id\n"
  let listFormatted ←
    Formatter.formatSourceWithEnv env listSource "balanced-list-like-items.lean"
  assertEq "broken list delimiters break every item" listExpected listFormatted

  let peerSource :=
    "def tupleCollection := (firstItemWithEnoughCharactersToRequireBalancedLayout, secondItemWithEnoughCharactersToRequireBalancedLayout, thirdItemWithEnoughCharactersToRequireBalancedLayout)\n"
    ++ "\n"
    ++ "def anonymousCollection := ⟨firstItemWithEnoughCharactersToRequireBalancedLayout, secondItemWithEnoughCharactersToRequireBalancedLayout, thirdItemWithEnoughCharactersToRequireBalancedLayout⟩\n"
  let peerExpected :=
    "def tupleCollection :=\n"
    ++ "  (\n"
    ++ "    firstItemWithEnoughCharactersToRequireBalancedLayout,\n"
    ++ "    secondItemWithEnoughCharactersToRequireBalancedLayout,\n"
    ++ "    thirdItemWithEnoughCharactersToRequireBalancedLayout\n"
    ++ "  )\n"
    ++ "\n"
    ++ "def anonymousCollection :=\n"
    ++ "  ⟨\n"
    ++ "    firstItemWithEnoughCharactersToRequireBalancedLayout,\n"
    ++ "    secondItemWithEnoughCharactersToRequireBalancedLayout,\n"
    ++ "    thirdItemWithEnoughCharactersToRequireBalancedLayout\n"
    ++ "  ⟩\n"
  let peerFormatted ←
    Formatter.formatSourceWithEnv env peerSource "balanced-tuple-like-items.lean"
  assertEq "tuple-like delimiters and items break together" peerExpected peerFormatted

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

def assertInfixAlternativeSequenceFlows (env : Lean.Environment) : IO Unit := do
  let source :=
    "def isMonotoneKind (kind : Name) : Bool :=\n"
    ++ "  if kind matches `Monotone | `Antitone | `StrictMono | `StrictAnti | `MonotoneOn | `AntitoneOn | `StrictMonoOn | `StrictAntiOn then true else false\n"
  let expected :=
    "def isMonotoneKind (kind : Name) : Bool :=\n"
    ++ "  if kind\n"
    ++ "      matches\n"
    ++ "      `Monotone | `Antitone | `StrictMono | `StrictAnti\n"
    ++ "      | `MonotoneOn | `AntitoneOn | `StrictMonoOn\n"
    ++ "      | `StrictAntiOn then\n"
    ++ "    true\n"
    ++ "  else\n"
    ++ "    false\n"
  let formatted ←
    Formatter.formatSourceWithEnv env source "infix-alternative-sequence.lean"
      { lineWidth := 60 }
  assertEq "infix RHS alternatives flow before bars" expected formatted
  assertTrue "infix RHS alternative formatting preserves code"
    (← codePreservedIgnoringWhitespace env source formatted)
  let moduleTree ←
    SyntaxTree.parseModuleStringWithEnv env formatted
      "infix-alternative-sequence-formatted.lean"
  assertTrue "infix RHS alternative formatting avoids overflow"
    (Formatter.Diagnostics.overflowOccurrences moduleTree { lineWidth := 60 }).isEmpty
  let formattedAgain ←
    Formatter.formatSourceWithEnv env formatted
      "infix-alternative-sequence-formatted.lean" { lineWidth := 60 }
  assertEq "infix RHS alternative formatting is idempotent" formatted formattedAgain

def assertInfixIgnoresFittingSourceBreaks (env : Lean.Environment) : IO Unit := do
  let source :=
    "def sourceBreakInfix : Prop :=\n" ++ "  firstCondition\n" ++ "  ∧ secondCondition\n"
  let expected :=
    "def sourceBreakInfix : Prop :=\n" ++ "  firstCondition ∧ secondCondition\n"
  let formatted ← Formatter.formatSourceWithEnv env source "infix-source-breaks.lean"
  assertEq "infix ignores fitting source breaks" expected formatted

def assertInfixIgnoresArbitrarySourceBreaks (env : Lean.Environment) : IO Unit := do
  let source :=
    "def arbitraryInfixSourceBreak : Prop := firstCondition ∧\n" ++ "  secondCondition\n"
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
  let formatted ← Formatter.formatSourceWithEnv env source "selection-directive-free.lean"
  assertEq "infix RHS fits before source breaks" expected formatted

def assertLogicalArrowSourceBreakIdempotent (env : Lean.Environment) : IO Unit := do
  let source :=
    "def logicalArrowSourceBreak : Prop :=\n"
    ++ "  schema.typesOverlapBool parentType typeCondition = true ->\n"
    ++ "    ∀ objectType, bodyWithAdditionalContext objectType contextValue\n"
  let expected :=
    "def logicalArrowSourceBreak : Prop :=\n"
    ++ "  schema.typesOverlapBool parentType typeCondition = true\n"
    ++ "  -> ∀ objectType, bodyWithAdditionalContext objectType contextValue\n"
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
    ++ "      veryLongSourceArgumentName\n"
    ++ "      = Execution.executeQueryWithFuel schema resolvers variableValues\n"
    ++ "          (completeNormalizeOperation schema operation) fuel source\n"
  let expected :=
    "def equalityInWrappedImplicationOperand : Prop :=\n"
    ++ "  operationBoolVarsComplete operation variableValues\n"
    ++ "  -> Execution.executeQueryWithFuel schema resolvers variableValues operation fuel\n"
    ++ "        veryLongSourceArgumentName\n"
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
    Formatter.formatSourceWithEnv env once "application-flow-infix-depth-idempotent.lean"
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

def assertParenthesizedQuantifierBlockIgnoresParentInfixLeftDepth (env : Lean.Environment)
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

def assertApplicationInNestedInfixKeepsHierarchy (env : Lean.Environment) : IO Unit := do
  let source :=
    "def nestedApplicationConsAppend : Prop :=\n"
    ++ "  premise\n"
    ++ "  -> VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues\n"
    ++ "      depth parentType source\n"
    ++ "      (Selection.field responseName fieldName arguments fieldDirectives\n"
    ++ "          veryLongFieldSelectionSetName\n"
    ++ "        :: inlineSelectionSet\n"
    ++ "        ++ rest)\n"
  let expected :=
    "def nestedApplicationConsAppend : Prop :=\n"
    ++ "  premise\n"
    ++ "  -> VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues\n"
    ++ "      depth parentType source\n"
    ++ "      (Selection.field responseName fieldName arguments fieldDirectives\n"
    ++ "            veryLongFieldSelectionSetName\n"
    ++ "          :: inlineSelectionSet\n"
    ++ "        ++ rest)\n"
  let formatted ←
    Formatter.formatSourceWithEnv env source "application-in-nested-infix-hierarchy.lean"
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

def assertElseIfChainBreaksThenBranchesTogether (env : Lean.Environment) : IO Unit := do
  let source :=
    "def toffoliMulBasis (i : Fin 8) : Result :=\n"
    ++ "  Vector.basis\n"
    ++ "    ( if i = (6 : Fin 8) then\n"
    ++ "        (7 : Fin 8)\n"
    ++ "      else if i = (7 : Fin 8) then (6 : Fin 8) else if i = (5 : Fin 8) then (4 : Fin 8) else i)\n"
  let expected :=
    "def toffoliMulBasis (i : Fin 8) : Result :=\n"
    ++ "  Vector.basis\n"
    ++ "    (if i = (6 : Fin 8) then\n"
    ++ "        (7 : Fin 8)\n"
    ++ "      else if i = (7 : Fin 8) then\n"
    ++ "        (6 : Fin 8)\n"
    ++ "      else if i = (5 : Fin 8) then\n"
    ++ "        (4 : Fin 8)\n"
    ++ "      else\n"
    ++ "        i)\n"
  let formatted ←
    Formatter.formatSourceWithEnv env source "else-if-chain-then-branches.lean"
  assertEq "else-if chain breaks then branches together" expected formatted

def assertTermMatchAlternativesStayOnOwnLines (env : Lean.Environment) : IO Unit := do
  let source :=
    "def lookupVariableValue? : Option InputValue :=\n"
    ++ "  match variableValues with\n"
    ++ "  | [] => none\n"
    ++ "  | (variableName, value) :: rest => value\n"
  let formatted ← Formatter.formatSourceWithEnv env source "term-match-alternatives.lean"
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

def assertParenthesizedIfKeepsTightHeadAndAlignedBranches (env : Lean.Environment)
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
    ++ "    (if buildExit == 0 && commentExit == 0 && styleExit == 0 && leanExit == 0 then\n"
    ++ "        0\n"
    ++ "      else\n"
    ++ "        1)\n"
  let formatted ←
    Formatter.formatSourceWithEnv env source "parenthesized-if-alignment.lean"
  assertEq "parenthesized if keeps tight head and aligned branches" expected formatted

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
  let formatted ← Formatter.formatSourceWithEnv env source "match-discriminants-flow.lean"
  assertEq "match discriminants align under the first discriminant" expected formatted
  let parenthesizedSource :=
    "theorem resolveBoth\n"
    ++ "    : Result\n"
    ++ "      -> (match schema.lookupField sourceField.parentType sourceField.fieldName,\n"
    ++ "                resolvers.resolve sourceField.parentType sourceField.fieldName\n"
    ++ "                  sourceField.arguments source with\n"
    ++ "          | some fieldDefinition, some value => completeValue fieldDefinition value\n"
    ++ "          | _, _ => defaultValue) := by\n"
    ++ "  exact proof\n"
  let parenthesizedFormatted ←
    Formatter.formatSourceWithEnv env parenthesizedSource
      "parenthesized-match-discriminants.lean"
  assertEq "parenthesized match discriminants retain first-discriminant alignment"
    parenthesizedSource parenthesizedFormatted
  let longMotiveSource :=
    "theorem longMotive {o : ONote} {x} (e : fundamentalSequence o = x)\n"
    ++ "    : fastGrowing o\n"
    ++ "      = match (motive := (x : Option ONote ⊕ (Nat → ONote)) → FundamentalSequenceProp o x → Nat → Nat) x,\n"
    ++ "          e ▸ fundamentalSequence_has_prop o with\n"
    ++ "        | Sum.inl none, _ => Nat.succ\n"
    ++ "        | Sum.inl (some a), _ => fun i => fastGrowing a i\n"
    ++ "        | Sum.inr f, _ => fun i => fastGrowing (f i) i := by\n"
    ++ "  simp\n"
  let longMotiveExpected :=
    "theorem longMotive {o : ONote} {x} (e : fundamentalSequence o = x)\n"
    ++ "    : fastGrowing o\n"
    ++ "      = match (motive := (x : Option ONote ⊕ (Nat → ONote))\n"
    ++ "                          → FundamentalSequenceProp o x → Nat → Nat) x,\n"
    ++ "        e ▸ fundamentalSequence_has_prop o with\n"
    ++ "        | Sum.inl none, _ => Nat.succ\n"
    ++ "        | Sum.inl (some a), _ => fun i => fastGrowing a i\n"
    ++ "        | Sum.inr f, _ => fun i => fastGrowing (f i) i := by\n"
    ++ "  simp\n"
  let longMotiveFormatted ←
    Formatter.formatSourceWithEnv env longMotiveSource
      "long-match-motive-discriminants.lean" { lineWidth := 100 }
  assertEq "match discriminants after a motive use the match base"
    longMotiveExpected longMotiveFormatted
  let longMotiveModule ←
    SyntaxTree.parseModuleStringWithEnv env longMotiveFormatted
      "long-match-motive-discriminants-formatted.lean"
  assertTrue "long match motive discriminants avoid overflow"
    (Formatter.Diagnostics.overflowOccurrences longMotiveModule
      { lineWidth := 100 }).isEmpty
  let longMotiveFormattedAgain ←
    Formatter.formatSourceWithEnv env longMotiveFormatted
      "long-match-motive-discriminants-formatted.lean" { lineWidth := 100 }
  assertEq "long match motive discriminants are idempotent"
    longMotiveFormatted longMotiveFormattedAgain

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
    Formatter.formatSourceWithEnv env source "match-discriminant-application-indent.lean"
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

def assertPrefixedMatchAlternativesAlignWithMatch (env : Lean.Environment) : IO Unit := do
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
    "def nestedOptionMatchInListMatch (selectionSet : List Nat) (field? : Option Nat) : Prop :=\n"
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

def assertBreakNeverPrecedesTrailingSeparator (env : Lean.Environment) : IO Unit := do
  let source :=
    "def separatorBreak (values : List Nat) : Prop :=\n"
    ++ "  ∀ value ∈ values.filter (fun candidate => candidate = candidate), value = value\n"
  let expected :=
    "def separatorBreak (values : List Nat) : Prop :=\n"
    ++ "  ∀ value ∈\n"
    ++ "            values.filter\n"
    ++ "              (fun candidate => candidate = candidate), value\n"
    ++ "                                                        = value\n"
  let formatted ←
    Formatter.formatSourceWithEnv env source "trailing-separator-break.lean"
      { lineWidth := 55 }
  assertEq "line breaks are not inserted immediately before separators" expected formatted

def assertQuantifierIdentifierSequenceFlows (env : Lean.Environment) : IO Unit := do
  let source :=
    "def quantifiedPrefixes : Prop := ∃ leftPrefixFields leftPrefixErrors "
    ++ "rightPrefixFields rightPrefixErrors leftSuffixFields leftSuffixErrors "
    ++ "rightSuffixFields rightSuffixErrors, True\n"
  let expected :=
    "def quantifiedPrefixes : Prop :=\n"
    ++ "  ∃ leftPrefixFields leftPrefixErrors rightPrefixFields rightPrefixErrors leftSuffixFields\n"
    ++ "      leftSuffixErrors rightSuffixFields rightSuffixErrors,\n"
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

def assertGuardMsgsCommandUsesCommandInLayout (env : Lean.Environment) : IO Unit := do
  let source :=
    "/-- info: value : Nat -/\n"
    ++ "#guard_msgs in\n" ++ "#check (sorry : Nat)\n"
  let formatted ← Formatter.formatSourceWithEnv env source "guard-msgs-command.lean"
  assertEq "guard messages command uses command in layout" source formatted
  let moduleTree ←
    SyntaxTree.parseModuleStringWithEnv env formatted "guard-msgs-command-formatted.lean"
  assertTrue "guard messages command has complete rule coverage"
    (Formatter.Diagnostics.missingRuleOccurrencesForModule moduleTree).isEmpty
  let formattedAgain ←
    Formatter.formatSourceWithEnv env formatted "guard-msgs-command-formatted-again.lean"
  assertEq "guard messages command is idempotent" formatted formattedAgain

def assertBinderTacticProofBodyHasNoMissingRules (env : Lean.Environment) : IO Unit := do
  let source := "def binderTacticDefault (h : True := by simp) : Nat := 0\n"
  let moduleTree ←
    SyntaxTree.parseModuleStringWithEnv env source "binder-tactic-default.lean"
  assertTrue "binder tactic proof body has complete rule coverage"
    (Formatter.Diagnostics.missingRuleOccurrencesForModule moduleTree).isEmpty
  let formatted ← Formatter.formatSourceWithEnv env source "binder-tactic-default.lean"
  assertEq "binder tactic default remains compact" source formatted

def assertInstanceValueInheritsDeclarationBase (env : Lean.Environment) : IO Unit := do
  let source :=
    "noncomputable instance : Module A B :=\n"
    ++ "  letI (i : I) : Module C D := by\n"
    ++ "    dsimp; infer_instance\n"
    ++ "  finalValue x\n"
  let formatted ← Formatter.formatSourceWithEnv env source "nested-let-proof-body.lean"
  assertEq "instance values use the declaration base" source formatted

def assertSufficesBodyBreaksAfterFromProof (env : Lean.Environment) : IO Unit := do
  let directSource :=
    "def sample : Result :=\n"
    ++ "  suffices left = right from useProof this\n"
    ++ "  nextTerm argument\n"
  let directFormatted ←
    Formatter.formatSourceWithEnv env directSource "suffices-body.lean"
  assertEq "suffices body stays separate from its from proof" directSource directFormatted
  let nestedSource :=
    "theorem nestedSuffices : Result :=\n"
    ++ "  outer <|\n"
    ++ "    suffices left = right from\n"
    ++ "      useProof this\n"
    ++ "    nextTerm argument fun i => by\n"
    ++ "      exact proof\n"
  let nestedFormatted ←
    Formatter.formatSourceWithEnv env nestedSource "nested-suffices-body.lean"
  assertTrue "nested suffices formatting preserves code"
    (← codePreservedIgnoringWhitespace env nestedSource nestedFormatted)
  assertTextContains "nested suffices body remains offside"
    nestedFormatted "\n  nextTerm argument"
  let nestedFormattedAgain ←
    Formatter.formatSourceWithEnv env nestedFormatted "nested-suffices-body.lean"
  assertEq "nested suffices formatting is idempotent" nestedFormatted nestedFormattedAgain

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
  let formatted ← Formatter.formatSourceWithEnv env source "arrow-quantifier-operand.lean"
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
  let existentialSource :=
    "theorem quantifierBinderOverflow : ∃ (ι : Type u) (_ : Fintype ι) (_ : DecidableEq ι) (p : ι → R) (_ : ∀ i, Irreducible <| p i) (e : ι → ℕ), DirectSum.IsInternal fun i => torsionBy R M <| p i ^ e i := by\n"
    ++ "  exact proof\n"
  let existentialExpected :=
    "theorem quantifierBinderOverflow\n"
    ++ "    : ∃ (ι : Type u) (_ : Fintype ι) (_ : DecidableEq ι) (p : ι → R) (_ : ∀ i, Irreducible <| p i)\n"
    ++ "            (e : ι → ℕ),\n"
    ++ "        DirectSum.IsInternal fun i => torsionBy R M <| p i ^ e i := by\n"
    ++ "  exact proof\n"
  let existentialFormatted ←
    Formatter.formatSourceWithEnv env existentialSource
      "existential-binder-sequence-break.lean" { lineWidth := 100 }
  assertEq "existential binder wrapper breaks between binders"
    existentialExpected existentialFormatted
  let moduleTree ←
    SyntaxTree.parseModuleStringWithEnv env existentialFormatted
      "existential-binder-sequence-break.lean"
  assertTrue "existential binder sequence has no overflow"
    (Formatter.Diagnostics.overflowOccurrences moduleTree { lineWidth := 100 }).isEmpty

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

def assertClassInductiveAlternativesStaySeparated (env : Lean.Environment) : IO Unit := do
  let source :=
    "class inductive ClassInductiveLayout : Nat → Prop where\n"
    ++ "  | zero : ClassInductiveLayout 0\n"
    ++ "  | succ (n : Nat) (h : ClassInductiveLayout n) : ClassInductiveLayout (n + 1)\n"
  let formatted ←
    Formatter.formatSourceWithEnv env source "class-inductive-alternatives.lean"
  assertEq "class inductive alternatives stay separated" source formatted

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

def assertStructureExtendsBreaksBeforeWhereFields (env : Lean.Environment) : IO Unit := do
  let source :=
    "structure VeryLongStructureName (R : Type u) (A : Type v) [CommSemiring R] [Semiring A] [Algebra R A] : Type v extends ParentStructureName A where\n"
    ++ "  field : Nat\n"
  let expected :=
    "structure VeryLongStructureName (R : Type u) (A : Type v) [CommSemiring R] [Semiring A]\n"
    ++ "    [Algebra R A]\n"
    ++ "    : Type v\n"
    ++ "    extends ParentStructureName A where\n"
    ++ "  field : Nat\n"
  let formatted ← Formatter.formatSourceWithEnv env source "structure-extends-rule.lean"
  assertEq "structure extends breaks before where fields" expected formatted

  let multipleParentsSource :=
    "structure MultipleParentStructure (A : Type) extends FirstLongParentName A, SecondLongParentName A,\n"
    ++ "    ThirdLongParentName A, FourthLongParentName A, FifthLongParentName A where\n"
    ++ "  marker : Nat\n"
    ++ "\n"
    ++ "def forceAnotherPass : Nat :=\n"
    ++ "value\n"
  let multipleParentsExpected :=
    "structure MultipleParentStructure (A : Type)\n"
    ++ "    extends FirstLongParentName A, SecondLongParentName A,\n"
    ++ "      ThirdLongParentName A, FourthLongParentName A, FifthLongParentName A where\n"
    ++ "  marker : Nat\n"
    ++ "\n"
    ++ "def forceAnotherPass : Nat :=\n"
    ++ "  value\n"
  let multipleParentsResult ←
    Formatter.formatSourceWithEnvDetailed env multipleParentsSource
      "structure-multiple-parents.lean" { lineWidth := 100 }
  assertTrue "multiple structure parents do not fall back"
    (!multipleParentsResult.fellBack)
  assertEq "multiple structure parents flow after commas"
    multipleParentsExpected multipleParentsResult.formatted
  let multipleParentsModule ←
    SyntaxTree.parseModuleStringWithEnv env multipleParentsResult.formatted
      "structure-multiple-parents-formatted.lean"
  assertTrue "multiple structure parents have no overflow"
    (Formatter.Diagnostics.overflowOccurrences multipleParentsModule
      { lineWidth := 100 }).isEmpty
  let multipleParentsFormattedAgain ←
    Formatter.formatSourceWithEnv env multipleParentsResult.formatted
      "structure-multiple-parents-formatted-again.lean" { lineWidth := 100 }
  assertEq "multiple structure parent formatting is idempotent"
    multipleParentsResult.formatted multipleParentsFormattedAgain

def assertShortStructureExtendsHeaderStaysFlat (env : Lean.Environment) : IO Unit := do
  let source :=
    "structure Candidate extends CandidateKey where\n"
    ++ "  occurrenceCount : Nat\n"
    ++ "deriving Repr\n"
  let formatted ←
    Formatter.formatSourceWithEnv env source "short-structure-extends-header.lean"
  assertEq "short structure extends header stays flat" source formatted
  let withoutDeriving :=
    "structure ParameterizedCandidate (α : Type) extends CandidateKey α where\n"
    ++ "  occurrenceCount : Nat\n"
  let withoutDerivingFormatted ←
    Formatter.formatSourceWithEnv env withoutDeriving
      "short-parameterized-structure-extends-header.lean"
  assertEq "short parameterized structure header stays flat before mandatory field breaks"
    withoutDeriving withoutDerivingFormatted

def assertStructureExtendsDoesNotIndentFollowingCommand (env : Lean.Environment)
    : IO Unit := do
  let source :=
    "structure Child\n"
    ++ "    extends Parent where\n"
    ++ "  field : Nat\n"
    ++ "\n"
    ++ "/-- The following command remains at the command base. -/\n"
    ++ "#check Nat\n"
  let formatted ←
    Formatter.formatSourceWithEnv env source "structure-extends-following-command.lean"
  assertEq "structure extends does not indent the following command" source formatted

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

  let multipleSources :=
    "def combined : Target :=\n"
    ++ "  { (firstParent argument),\n"
    ++ "    (secondParent firstArgument secondArgument thirdArgument fourthArgument) with\n"
    ++ "    field := value }\n"
  let multipleSourcesExpected :=
    "def combined : Target :=\n"
    ++ "  {\n"
    ++ "    (firstParent argument),\n"
    ++ "    (secondParent firstArgument secondArgument thirdArgument fourthArgument) with\n"
    ++ "      field := value\n"
    ++ "  }\n"
  let multipleSourcesTree ←
    SyntaxTree.parseModuleStringWithEnv env multipleSources
      "struct-update-multiple-sources.lean"
  assertTrue "structure update parents are direct children"
    (multipleSourcesTree.tree.firstNodeChildCount? .structureUpdate == some 4)
  let multipleSourcesFormatted ←
    Formatter.formatSourceWithEnv env multipleSources
      "struct-update-multiple-sources.lean"
  assertEq "multiple structure update sources align"
    multipleSourcesExpected multipleSourcesFormatted

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
  assertTextContains "CLI help documents line-width override"
    LeanFmt.Cli.usage "--line-width"
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
      throw <| IO.userError s!"CLI parser should accept --check and files: {repr result}"
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
  match LeanFmt.Cli.parseArgs ["--worker-batch-size", "8", "GraphQL.lean"] with
  | .run options =>
      assertTrue "CLI worker batch size flag" (options.workerBatchSize? == some 8)
      assertTrue "CLI worker batch size does not imply dry run" (!options.check)
  | result =>
      throw
      <| IO.userError
          s!"CLI parser should accept --worker-batch-size and files: {repr result}"
  match LeanFmt.Cli.parseArgs ["--line-width", "100", "GraphQL.lean"] with
  | .run options =>
      assertTrue "CLI line-width flag" (options.formatterOptions.lineWidth == 100)
  | result =>
      throw
      <| IO.userError s!"CLI parser should accept --line-width and files: {repr result}"

def assertLineWidthOptionAffectsFormatting (env : Lean.Environment) : IO Unit := do
  let source :=
    "def wideApplication := veryLongFunctionName firstArgument secondArgument thirdArgument\n"
  let narrow ←
    Formatter.formatSourceWithEnv env source "line-width-option.lean" { lineWidth := 40 }
  let wide ←
    Formatter.formatSourceWithEnv env source "line-width-option.lean" { lineWidth := 120 }
  assertTrue "line-width option changes rendered layout" (narrow != wide)
  assertEq "wide line-width option keeps fitting source flat" source wide
  let _ ← SyntaxTree.parseModuleStringWithEnv env narrow "line-width-option.lean"
  match LeanFmt.Cli.parseArgs ["--env-cache-size", "0", "GraphQL.lean"] with
  | .run options =>
      assertTrue "CLI environment cache size flag" (options.environmentCacheSize == 0)
  | result =>
      throw
      <| IO.userError
          s!"CLI parser should accept --env-cache-size and files: {repr result}"
  match LeanFmt.Cli.parseArgs ["--worker-batch-size", "0", "GraphQL.lean"] with
  | .error "invalid --worker-batch-size value: 0" => pure ()
  | result =>
      throw
      <| IO.userError
          s!"CLI parser should reject invalid --worker-batch-size: {repr result}"
  match LeanFmt.Cli.parseArgs ["--import-env-first", "GraphQL.lean"] with
  | .run options =>
      assertTrue "CLI import environment first flag" options.importEnvFirst
  | result =>
      throw
      <| IO.userError
          s!"CLI parser should accept --import-env-first and files: {repr result}"
  match LeanFmt.Cli.parseArgs ["--profile", "GraphQL.lean"] with
  | .run options =>
      assertTrue "public CLI profile flag" options.profile
      assertTrue "public CLI profile does not imply no-write check" (!options.check)
  | result =>
      throw <| IO.userError s!"public CLI should accept --profile, got: {repr result}"
  for testOnlyOption in ["--update-fixture", "--trace-renderer"] do
    match LeanFmt.Cli.parseArgs [testOnlyOption, "GraphQL.lean"] with
    | .error message =>
        assertEq s!"public CLI rejects {testOnlyOption}"
          s!"unknown option: {testOnlyOption}" message
    | result =>
        throw
        <| IO.userError s!"public CLI should reject {testOnlyOption}, got: {repr result}"
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
  let keys (entries : List (String × Lean.Environment)) : String :=
    String.intercalate "," (entries.map Prod.fst)
  let entries ← IO.mkRef []
  let cache : LeanFmt.Driver.EnvironmentCache :=
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
  let disabledCache : LeanFmt.Driver.EnvironmentCache :=
    { default := env, maxEntries := 0, entries := disabledEntries }
  disabledCache.rememberEnvironment "ignored" env
  assertTrue "disabled environment cache remains empty" (← disabledEntries.get).isEmpty

def assertDefaultEnvironmentPartition (env : Lean.Environment) : IO Unit := do
  IO.FS.withTempDir
    fun root =>
      do
        let entries ← IO.mkRef []
        let cache : LeanFmt.Driver.EnvironmentCache :=
          { default := env, maxEntries := 1, entries }
        let ordinary := root / "Ordinary.lean"
        let importedSyntax := root / "ImportedSyntax.lean"
        IO.FS.writeFile ordinary "import Missing.Module\n\ndef ordinary : Nat := 0\n"
        IO.FS.writeFile importedSyntax
          "import Missing.Module\n\ntheorem product : lhs ⬝ rhs := by trivial\n"
        let (defaultFiles, importFiles) ←
          LeanFmt.Driver.partitionDefaultEnvironmentFiles cache [ordinary, importedSyntax]
        assertEq "ordinary imported files use the default environment"
          (toString [ordinary]) (toString defaultFiles)
        assertEq "unknown imported syntax requires the import environment"
          (toString [importedSyntax]) (toString importFiles)

def assertWorkersUseInputLakeRoot : IO Unit := do
  IO.FS.withTempDir
    fun root =>
      do
        let project := root / "external-project"
        let nested := project / "QuantumComputing" / "Gates"
        IO.FS.createDirAll nested
        IO.FS.writeFile (project / "lakefile.toml") "name = \"external_project\"\n"
        IO.FS.writeFile (project / "lake-manifest.json")
          "{\"packages\":[{\"name\":\"mathlib\"}],\"name\":\"external_project\"}\n"
        let file := nested / "Projectors.lean"
        IO.FS.writeFile file "def projector : Nat := 0\n"
        let otherFile := nested / "Actions.lean"
        IO.FS.writeFile otherFile "def action : Nat := 0\n"
        let cwd? ←
          LeanFmt.Driver.workerCwd?
            { recursive := true, files := [project / "QuantumComputing"] }
        assertEq "recursive worker uses containing Lake package root"
          (toString (some project)) (toString cwd?)
        let relativeProject := FilePath.mk ".lake" / "leanfmt-relative-worker-root-test"
        IO.FS.createDirAll (relativeProject / "QuantumComputing")
        IO.FS.writeFile (relativeProject / "lakefile.toml")
          "name = \"relative_worker_root_test\"\n"
        let relativeCwd? ←
          LeanFmt.Driver.workerCwd?
            {
              recursive := true,
              files :=
                [relativeProject / "QuantumComputing", relativeProject / "lakefile.toml"]
            }
        let currentDir ← IO.currentDir
        assertEq "relative recursive worker inputs use containing Lake package root"
          (toString (some (currentDir / relativeProject).normalize))
          (toString (relativeCwd?.map (·.normalize)))
        let explicitCwd? ← LeanFmt.Driver.workerCwd? { files := [file, otherFile] }
        assertEq "explicit files use their common Lake package root"
          (toString (some project)) (toString explicitCwd?)
        assertTrue "recursive external package uses worker even for one large batch"
          (LeanFmt.Driver.shouldUseWorker
            {
              recursive := true,
              workerBatchSize? := some 100,
              files := [project / "QuantumComputing"]
            }
            cwd? 2)
        assertTrue "explicit multi-file package invocation uses workers"
          (LeanFmt.Driver.shouldUseWorker { files := [file, otherFile] } explicitCwd? 2)
        assertTrue "single-file package invocation stays in process"
          (!LeanFmt.Driver.shouldUseWorker { files := [file] } explicitCwd? 1)
        assertTrue "worker subprocess does not spawn nested workers"
          (!LeanFmt.Driver.shouldUseWorker { worker := true } explicitCwd? 2)
        let otherProject := root / "other-project"
        IO.FS.createDirAll otherProject
        IO.FS.writeFile (otherProject / "lakefile.toml") "name = \"other_project\"\n"
        let otherProjectFile := otherProject / "Other.lean"
        IO.FS.writeFile otherProjectFile "def other : Nat := 0\n"
        let crossPackageCwd? ←
          LeanFmt.Driver.workerCwd? { files := [file, otherProjectFile] }
        assertTrue "files from different packages do not share a worker cwd"
          crossPackageCwd?.isNone
        assertTrue
          "invocation without a package root or explicit batch stays in process"
          (!LeanFmt.Driver.shouldUseWorker { recursive := true } none 100)
        assertTrue "explicit batch size enables workers without recursive traversal"
          (LeanFmt.Driver.shouldUseWorker { workerBatchSize? := some 16 } none 100)
        assertTrue "external package starts with all remaining files"
          ((← LeanFmt.Driver.initialWorkerBatchSize
                { recursive := true, files := [project / "QuantumComputing"] }
                cwd? [file, otherFile])
            == 2)
        let workerPaths ← LeanFmt.Driver.pathsForWorkerCwd cwd? [file, otherFile]
        assertEq "recursive external worker paths are relative to worker cwd"
          (toString
            [
              FilePath.mk "QuantumComputing/Gates/Projectors.lean",
              FilePath.mk "QuantumComputing/Gates/Actions.lean"
            ])
          (toString workerPaths)
        assertTrue "explicit recursive external worker batch size overrides default"
          ((← LeanFmt.Driver.initialWorkerBatchSize
                {
                  recursive := true,
                  workerBatchSize? := some 4,
                  files := [project / "QuantumComputing"]
                }
                cwd? [file, otherFile])
            == 4)
        IO.FS.writeFile (project / "lake-manifest.json")
          "{\"packages\":[{\"name\":\"other\"}],\"name\":\"external_project\"}\n"
        assertTrue "external package without Mathlib starts with all remaining files"
          ((← LeanFmt.Driver.initialWorkerBatchSize
                { recursive := true, files := [project / "QuantumComputing"] }
                cwd? [file, otherFile])
            == 2)

def assertImportFilesGroupByHeader : IO Unit := do
  IO.FS.withTempDir
    fun root =>
      do
        let first := root / "First.lean"
        let second := root / "Second.lean"
        let third := root / "Third.lean"
        IO.FS.writeFile first "import Lean\n\ndef first : Nat := 0\n"
        IO.FS.writeFile second "import Init\n\ndef second : Nat := 0\n"
        IO.FS.writeFile third "import Lean\n\ndef third : Nat := 0\n"
        let groups ← LeanFmt.Driver.importFileGroups none [first, second, third]
        assertEq "import-heavy files group by normalized import header"
          (toString [[first, third], [second]]) (toString (groups.map (·.files)))

def assertImportFilesGroupByLakeSetupImportArtifacts : IO Unit := do
  IO.FS.withTempDir
    fun root =>
      do
        let project := root / "project"
        let sourceDir := project / "QuantumComputing"
        let setupDir := project / ".lake" / "build" / "ir" / "QuantumComputing"
        IO.FS.createDirAll sourceDir
        IO.FS.createDirAll setupDir
        let first := sourceDir / "First.lean"
        let second := sourceDir / "Second.lean"
        let third := sourceDir / "Third.lean"
        IO.FS.writeFile first "import QuantumComputing.Second\n\ndef first : Nat := 0\n"
        IO.FS.writeFile second "import Mathlib\n\ndef second : Nat := 0\n"
        IO.FS.writeFile third "import Lean\n\ndef third : Nat := 0\n"
        IO.FS.writeFile (setupDir / "First.setup.json")
          "{\"importArts\":{\"Mathlib\":{},\"QuantumComputing.Second\":{}}}\n"
        IO.FS.writeFile (setupDir / "Second.setup.json")
          "{\"importArts\":{\"Mathlib\":{}}}\n"
        IO.FS.writeFile (setupDir / "Third.setup.json") "{\"importArts\":{\"Lean\":{}}}\n"
        let groups ← LeanFmt.Driver.importFileGroups (some project) [first, second, third]
        assertEq "Lake setup import artifacts group by covering environment"
          (toString [[first, second], [third]]) (toString (groups.map (·.files)))
        assertEq "Lake setup import artifacts choose superset environment file"
          (toString [first, third]) (toString (groups.map (·.environmentFile)))

def assertImportFilesUseDefaultAggregatorAsEnvironmentCandidate : IO Unit := do
  IO.FS.withTempDir
    fun root =>
      do
        let project := root / "project"
        let sourceDir := project / "QuantumComputing"
        let setupDir := project / ".lake" / "build" / "ir"
        IO.FS.createDirAll sourceDir
        IO.FS.createDirAll (setupDir / "QuantumComputing")
        let aggregator := project / "QuantumComputing.lean"
        let first := sourceDir / "First.lean"
        let second := sourceDir / "Second.lean"
        IO.FS.writeFile aggregator
          "import QuantumComputing.First\nimport QuantumComputing.Second\n"
        IO.FS.writeFile first "import Mathlib\n\ndef first : Nat := 0\n"
        IO.FS.writeFile second "import Mathlib\n\ndef second : Nat := 0\n"
        IO.FS.writeFile (setupDir / "QuantumComputing.setup.json")
          "{\"importArts\":{\"Mathlib\":{},\"QuantumComputing.First\":{},\"QuantumComputing.Second\":{}}}\n"
        IO.FS.writeFile (setupDir / "QuantumComputing" / "First.setup.json")
          "{\"importArts\":{\"Mathlib\":{},\"QuantumComputing.First\":{}}}\n"
        IO.FS.writeFile (setupDir / "QuantumComputing" / "Second.setup.json")
          "{\"importArts\":{\"Mathlib\":{},\"QuantumComputing.Second\":{}}}\n"
        let groups ←
          LeanFmt.Driver.importFileGroupsWithEnvironmentCandidates
            (some project) [aggregator, first, second] [first, second]
        assertEq "default-parsing aggregator can cover imported files"
          (toString [[first, second]]) (toString (groups.map (·.files)))
        assertEq "default-parsing aggregator is selected as worker environment"
          (toString [aggregator]) (toString (groups.map (·.environmentFile)))

def assertRecursiveWorkerChecksTargetToolchain : IO Unit := do
  IO.FS.withTempDir
    fun root =>
      do
        let matching := root / "matching"
        IO.FS.createDirAll matching
        IO.FS.writeFile (matching / "lean-toolchain") LeanFmt.Driver.expectedLeanToolchain
        assertTrue "recursive worker accepts matching Lean toolchain"
          (← LeanFmt.Driver.checkWorkerToolchain (some matching))
        let mismatching := root / "mismatching"
        IO.FS.createDirAll mismatching
        IO.FS.writeFile (mismatching / "lean-toolchain")
          s!"{LeanFmt.Driver.expectedLeanToolchain}-mismatch\n"
        assertTrue "recursive worker rejects mismatching Lean toolchain"
          (!(← LeanFmt.Driver.checkWorkerToolchain (some mismatching)))

def assertFormattingExceptionChecks (env : Lean.Environment) : IO Unit := do
  assertTrue "whitespace-only edits preserve code"
    (← codePreservedIgnoringWhitespace env "def x : Nat := 0\n" "def   x:Nat:=0\n")
  assertTrue "token edits do not preserve code"
    (!(← codePreservedIgnoringWhitespace env "def x : Nat := 0\n" "def y : Nat := 0\n"))
  assertTrue "whitespace cannot move an identifier boundary"
    (!(← codePreservedIgnoringWhitespace env "def value := ab c\n" "def value := a bc\n"))
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
  assertTrue "overflow diagnostics respect custom line width"
    (Formatter.Diagnostics.overflowOccurrences overflowModule
      { lineWidth := 120 }).isEmpty
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
  let bareInterpolatedStringOverflow :=
    "def message := \""
    ++ String.ofList (List.replicate Formatter.maxLineWidth 'x')
    ++ "{value}\"\n"
  let bareInterpolatedStringModule ←
    SyntaxTree.parseModuleStringWithEnv env bareInterpolatedStringOverflow
      "bare-interpolated-string-overflow.lean"
  assertTrue "bare interpolated-string tree overflow is exempt"
    (Formatter.Diagnostics.overflowOccurrences bareInterpolatedStringModule).isEmpty
  let stringCommaOverflow :=
    "def messages := [\n  \""
    ++ String.ofList (List.replicate Formatter.maxLineWidth 'x')
    ++ "\",\n  \"short\",\n]\n"
  let stringCommaModule ←
    SyntaxTree.parseModuleStringWithEnv env stringCommaOverflow
      "string-comma-overflow.lean"
  assertTrue "string and trailing comma tree overflow is exempt"
    (Formatter.Diagnostics.overflowOccurrences stringCommaModule).isEmpty
  let atomicCommaOverflow := "def values := [\n  " ++ longIdentifier ++ ",\n  short,\n]\n"
  let atomicCommaModule ←
    SyntaxTree.parseModuleStringWithEnv env atomicCommaOverflow
      "atomic-comma-overflow.lean"
  assertTrue "atomic tree and trailing comma overflow is exempt"
    (Formatter.Diagnostics.overflowOccurrences atomicCommaModule).isEmpty
  let counts : LeanFmt.Driver.ExceptionCounts :=
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

def assertCliChecksStillFormatUnlessCheck
    (env : Lean.Environment) (cache : LeanFmt.Driver.EnvironmentCache)
    : IO Unit := do
  let root : FilePath := ".lake/leanfmt-cli-test/checks"
  IO.FS.createDirAll root
  let preservingFile := root / "Preserving.lean"
  let preservingSource := "def  preserving  : Nat := 0\n"
  IO.FS.writeFile preservingFile preservingSource
  let preservingExitCode ←
    LeanFmt.Driver.runOptionsWithCache cache
      { checkException := true, includeHidden := true, files := [preservingFile] }
  assertTrue "CLI exception check still formats" (preservingExitCode == 0)
  let preservingFormatted ←
    Formatter.formatSourceWithEnv env preservingSource preservingFile.toString
  assertEq "CLI exception check writes formatted output"
    preservingFormatted (← IO.FS.readFile preservingFile)

  let overflowFile := root / "Overflow.lean"
  let overflowSource :=
    "def " ++ String.ofList (List.replicate (Formatter.maxLineWidth + 1) 'x') ++ " := 0\n"
  IO.FS.writeFile overflowFile overflowSource
  let afterExceptionFile := root / "AfterException.lean"
  let afterExceptionSource := "def  afterException  : Nat := 0\n"
  IO.FS.writeFile afterExceptionFile afterExceptionSource
  let overflowExitCode ←
    LeanFmt.Driver.runOptionsWithCache cache
      {
        checkException := true
        includeHidden := true
        files := [overflowFile, afterExceptionFile]
      }
  assertTrue "CLI exception check rejects remaining overflow" (overflowExitCode == 1)
  let overflowFormatted ←
    Formatter.formatSourceWithEnv env overflowSource overflowFile.toString
  assertEq "CLI exception failure writes the checked candidate"
    overflowFormatted (← IO.FS.readFile overflowFile)
  let afterExceptionFormatted ←
    Formatter.formatSourceWithEnv env afterExceptionSource afterExceptionFile.toString
  assertEq "CLI continues with files after an exception"
    afterExceptionFormatted (← IO.FS.readFile afterExceptionFile)
  IO.FS.writeFile overflowFile overflowSource
  let checkedOverflowExitCode ←
    LeanFmt.Driver.runOptionsWithCache cache
      {
        check := true
        checkException := true
        includeHidden := true
        files := [overflowFile]
      }
  assertTrue "CLI checked exception still fails" (checkedOverflowExitCode == 1)
  assertEq "explicit check prevents writing a failing candidate"
    overflowSource (← IO.FS.readFile overflowFile)

  let idempotentFile := root / "Idempotent.lean"
  let idempotentSource := "def  idempotent  : Nat := 0\n"
  IO.FS.writeFile idempotentFile idempotentSource
  let idempotentExitCode ←
    LeanFmt.Driver.runOptionsWithCache cache
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
    LeanFmt.Driver.runOptionsWithCache cache
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
    LeanFmt.Driver.runOptionsWithCache cache
      { check := true, includeHidden := true, files := [checkedFile] }
  assertTrue "CLI ordinary --check still fails on formatting changes"
    (ordinaryCheckExitCode == 1)

def assertCliFormatsDirectory
    (env : Lean.Environment) (cache : LeanFmt.Driver.EnvironmentCache)
    : IO Unit := do
  let root : FilePath := ".lake/leanfmt-cli-test/nonrecursive"
  let nested : FilePath := root / "nested"
  IO.FS.createDirAll nested
  let topFile := root / "Top.lean"
  let nestedFile := nested / "Nested.lean"
  let topSource := "def  top  : Nat := 0\n"
  let nestedSource := "def  nested  : Nat := 0\n"
  IO.FS.writeFile topFile topSource
  IO.FS.writeFile nestedFile nestedSource
  let exitCode ←
    LeanFmt.Driver.runOptionsWithCache cache { includeHidden := true, files := [root] }
  assertTrue "CLI directory format succeeds" (exitCode == 0)
  let topFormatted ← Formatter.formatSourceWithEnv env topSource topFile.toString
  assertEq "CLI formats direct Lean files in directory" topFormatted
    (← IO.FS.readFile topFile)
  assertEq "CLI non-recursive directory formatting skips nested Lean files"
    nestedSource (← IO.FS.readFile nestedFile)

def assertCliFormatsDirectoryRecursively
    (env : Lean.Environment) (cache : LeanFmt.Driver.EnvironmentCache)
    : IO Unit := do
  let root : FilePath := ".lake/leanfmt-cli-test/recursive"
  let nested : FilePath := root / "nested"
  IO.FS.createDirAll nested
  let topFile := root / "Top.lean"
  let nestedFile := nested / "Nested.lean"
  let topSource := "def  top  : Nat := 0\n"
  let nestedSource := "def  nested  : Nat := 0\n"
  IO.FS.writeFile topFile topSource
  IO.FS.writeFile nestedFile nestedSource
  match LeanFmt.Cli.parseArgs
          ["-r", "--include-hidden", "--worker-batch-size", "1", root.toString] with
  | .run options =>
      let exitCode ← LeanFmt.Driver.runOptionsWithCache cache options
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
          LeanFmt.Driver.expandInputPaths { recursive := true, files := [root] }
        assertTrue "CLI discovers visible direct files"
          (defaultFiles.contains visibleFile)
        assertTrue "CLI discovers visible nested files"
          (defaultFiles.contains visibleNestedFile)
        assertTrue "CLI skips hidden files" (!defaultFiles.contains hiddenFile)
        assertTrue "CLI skips hidden directories"
          (!defaultFiles.contains hiddenNestedFile)

        let explicitHiddenFile ←
          LeanFmt.Driver.expandInputPaths { files := [hiddenNestedFile] }
        assertTrue "CLI processes an explicitly supplied file under a hidden directory"
          (explicitHiddenFile == [hiddenNestedFile])

        let hiddenChildFile := hiddenDir / ".Child.lean"
        IO.FS.writeFile hiddenChildFile "def child : Nat := 0\n"
        let explicitHiddenDirectory ←
          LeanFmt.Driver.expandInputPaths { recursive := true, files := [hiddenDir] }
        assertTrue "CLI enters an explicitly supplied hidden directory"
          (explicitHiddenDirectory.contains hiddenNestedFile)
        assertTrue "CLI still skips hidden entries inside an explicit hidden directory"
          (!explicitHiddenDirectory.contains hiddenChildFile)

        let includedFiles ←
          LeanFmt.Driver.expandInputPaths
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

def assertCliLoadsImportedSyntax (cache : LeanFmt.Driver.EnvironmentCache) : IO Unit := do
  let root : FilePath := ".lake/leanfmt-cli-test/project-env"
  IO.FS.createDirAll root
  let file := root / "ImportedSyntax.lean"
  let source := "import LeanFmt.Tests.ProjectSyntax\n\n#check project_syntax\n"
  IO.FS.writeFile file source
  let exitCode ←
    LeanFmt.Driver.runOptionsWithCache cache { includeHidden := true, files := [file] }
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
  let commandSource :=
    "def first := 0\n" ++ "structure Second where\n" ++ "  value : Nat\n"
  let commandModule ←
    SyntaxTree.parseModuleStringWithEnv env commandSource "trace-command-boundary.lean"
  let (commandFormatted, commandTrace) :=
    Formatter.Debug.formatModuleWithTrace commandModule
  assertTextContains "renderer trace command output has computed blank boundary"
    commandFormatted "def first := 0\n\nstructure Second where"
  assertTextContains "renderer trace follows computed command boundary"
    commandTrace "line 3 | structure Second where\n  path="

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
  let commandQuotation :=
    SyntaxTree.Tree.node (.raw `Lean.Parser.Command.quot)
      #[.leaf (syntheticAtomToken "`("), .leaf (syntheticAtomToken ")")]
  assertTrue "command quotations preserve their original layout"
    (Formatter.shouldEmitOriginalTree commandQuotation)
  let annotation :=
    SyntaxTree.Tree.node (.raw `Lean.Parser.Command.declModifiers)
      #[.leaf (syntheticAtomToken "@[")]
  let theoremBody :=
    SyntaxTree.Tree.node (.raw `group) #[.leaf (syntheticAtomToken "lemma")]
  let extendedTheorem := SyntaxTree.Tree.node (.raw `lemma) #[annotation, theoremBody]
  let wrappedExtendedTheorem :=
    SyntaxTree.Tree.node (.raw `Lean.Parser.Command.in) #[extendedTheorem]
  let regroupedWrappedTheorem := SyntaxTree.regroupTree wrappedExtendedTheorem
  assertTrue "extended declarations nested under command wrappers regroup annotations"
    (regroupedWrappedTheorem.containsNodeKind .annotatedDeclaration)
  let unsuppressWrapper :=
    SyntaxTree.Tree.node (.raw `commandUnsuppress_compilationIn_)
      #[
        .leaf (syntheticAtomToken "unsuppress_compilation"),
        .node (.raw `null) #[.leaf (syntheticAtomToken "in"), extendedTheorem]
      ]
  let regroupedUnsuppress := SyntaxTree.regroupTree unsuppressWrapper
  let unsuppressSegment := Formatter.LineBreakRules.Segment.ofTree regroupedUnsuppress
  let unsuppressRule := Formatter.LineBreakRules.formattingRuleFor regroupedUnsuppress
  assertTrue "command in wrapper flattens its optional payload"
    (unsuppressSegment.size == 3)
  assertTrue "command in wrapper breaks after in"
    (unsuppressRule.breakPoints context unsuppressSegment
      |>.any fun breakPoint => breakPoint.index == 2)
  let annotatedTheorem := SyntaxTree.regroupTopLevelCommandAnnotations extendedTheorem
  let annotatedSegment := Formatter.LineBreakRules.Segment.ofTree annotatedTheorem
  let annotatedRule := Formatter.LineBreakRules.formattingRuleFor annotatedTheorem
  assertTrue "extended top-level commands break after leading annotations"
    (annotatedRule.breakPoints context annotatedSegment
      |>.any fun breakPoint => breakPoint.index == 1)
  let docComment :=
    SyntaxTree.Tree.node (.raw `Lean.Parser.Command.docComment)
      #[.leaf (syntheticAtomToken "/-- Documented custom command. -/")]
  let documentedCustomCommand :=
    SyntaxTree.Tree.node (.raw `documentedCustomCommand)
      #[
        .node (.raw `null) #[docComment],
        .missing,
        .leaf (syntheticAtomToken "documented_custom_command")
      ]
  let annotatedCustomCommand :=
    SyntaxTree.regroupTopLevelCommandAnnotations documentedCustomCommand
  let customCommandSegment :=
    Formatter.LineBreakRules.Segment.ofTree annotatedCustomCommand
  let customCommandRule :=
    Formatter.LineBreakRules.formattingRuleFor annotatedCustomCommand
  assertTrue "top-level custom command doc comments regroup as annotations"
    (annotatedCustomCommand.containsNodeKind .annotatedDeclaration)
  assertTrue "top-level custom commands break after doc comments"
    (customCommandRule.breakPoints context customCommandSegment
      |>.any fun breakPoint => breakPoint.index == 1)

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

def assertLakeDslFormatting : IO Unit := do
  let env ← SyntaxTree.importEnvironment #[{ module := `Lake }]
  let source :=
    "import Lake\n"
    ++ "open Lake DSL\n"
    ++ "\n"
    ++ "package quantum where\n"
    ++ "  srcDir := \".\"\n"
    ++ "\n"
    ++ "require mathlib from git\n"
    ++ "  \"https://github.com/leanprover-community/mathlib4.git\" @ \"v4.32.0\"\n"
    ++ "\n"
    ++ "@[default_target]\n"
    ++ "lean_lib QuantumComputing where\n"
  let expected :=
    "import Lake\n"
    ++ "\n"
    ++ "open Lake DSL\n"
    ++ "\n"
    ++ "package quantum where\n"
    ++ "  srcDir := \".\"\n"
    ++ "\n"
    ++ "require mathlib from git\n"
    ++ "  \"https://github.com/leanprover-community/mathlib4.git\" @ \"v4.32.0\"\n"
    ++ "\n"
    ++ "@[default_target]\n"
    ++ "lean_lib QuantumComputing where\n"
  let formatted ← Formatter.formatSourceWithEnv env source "lakefile.lean"
  assertEq "Lake DSL commands preserve conventional layout" expected formatted
  let moduleTree ← SyntaxTree.parseModuleStringWithEnv env formatted "lakefile.lean"
  assertTrue "Lake DSL commands have complete rule dispatch"
    (Formatter.Diagnostics.missingRuleOccurrencesForModule moduleTree).isEmpty

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
      `Lean.Parser.Command.initialize,
      `Lean.Parser.Command.initializeKeyword,
      `Lean.guardMsgsCmd,
      `Lean.Parser.Command.elab_rules,
      `Lean.Linter.«command_Register_linter_set_:=_»,
      `Lean.Option.registerOption,
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
      `Lean.Parser.commandUnseal__,
      `Lean.Parser.Command.recommended_spelling,
      `Topology.nhdsGT,
      `Topology.nhdsLT,
      `Topology.nhdsNE,
      `Topology.nhdsLE,
      `Topology.nhdsGE,
      `Topology.IsOpen_of,
      `Topology.IsClosed_of,
      `Topology.closure_of,
      `Topology.Continuous_of,
      `Lean.«command__Unif_hint____Where_|_-⊢__»,
      `Lean.unifConstraintElem,
      `Lake.DSL.packageCommand,
      `Lake.DSL.leanLibCommand,
      `Lake.DSL.requireDecl,
      `Lake.DSL.identOrStr,
      `Lake.DSL.optConfig,
      `Lake.DSL.declValWhere,
      `Lake.DSL.depSpec,
      `Lake.DSL.depName,
      `Lake.DSL.fromClause,
      `Lake.DSL.fromSource,
      `Lake.DSL.fromGit,
      `lemma,
      `Lean.Parser.Term.explicit,
      `Lean.Parser.Term.noindex,
      `Lean.Parser.Term.explicitUniv,
      `Lean.Parser.Term.have,
      `Lean.Parser.Term.haveI,
      `Lean.Parser.Term.suffices,
      `Lean.Parser.Term.sufficesDecl,
      `Lean.Parser.Term.open,
      `Lean.Parser.Term.termReturn,
      `Lean.Parser.Term.panic,
      `Lean.Parser.Term.sorry,
      `Lean.Parser.Term.stateRefT,
      `Lean.Parser.Term.unreachable,
      `Lean.Parser.Term.typeOf,
      `Lean.Parser.Term.dynamicQuot,
      `Lean.Parser.Term.structInstFieldEqns,
      `Lean.Parser.Term.sort,
      `Lean.Parser.Term.letI,
      `Lean.Parser.Term.letPosOpt,
      `Lean.Parser.Term.letOpts,
      `Lean.Parser.Term.letOptNondep,
      `Lean.Parser.Term.doLetExpr,
      `Lean.Parser.Term.doLetRec,
      `Lean.Parser.Term.doIfLetBind,
      `Lean.Parser.Term.doHave,
      `Lean.Parser.Term.doContinue,
      `Lean.Parser.Term.doFinally,
      `Lean.Parser.Term.doWhile,
      `Lean.Parser.Term.inferInstanceAs,
      `Lean.Parser.Term.configItem,
      `Lean.Parser.Term.negConfigItem,
      `Lean.Parser.Term.doMatchExpr,
      `Lean.Parser.Term.doAssert,
      `Lean.Parser.Term.matchExprAlts,
      `Lean.Parser.Term.matchExprAlt,
      `Lean.Parser.Term.matchExprElseAlt,
      `Lean.Parser.Term.matchExprPat,
      `Lean.Parser.Term.strictImplicitBinder,
      `Lean.Parser.Term.nofun,
      `Lean.Parser.Term.doNested,
      `Lean.Parser.Term.doSeqBracketed,
      `Lean.Parser.Term.whereFinally,
      `Lean.Parser.Tactic.tacticSeq,
      `Lean.Parser.Tactic.tacticSeq1Indented,
      `Lean.Parser.Tactic.tacticRwa__,
      `Lean.Parser.Tactic.rwRuleSeq,
      `Lean.Parser.Tactic.rwRule,
      `Lean.Parser.Tactic.location,
      `Lean.Parser.Tactic.locationHyp,
      `Lean.Parser.Tactic.exact,
      `Lean.Parser.Tactic.tacticRfl,
      `Lean.Parser.Tactic.grind,
      `Lean.Parser.Tactic.optConfig,
      `Lean.Parser.Tactic.posConfigItem,
      `Lean.Parser.Tactic.negConfigItem,
      `Lean.Parser.Tactic.valConfigItem,
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
      `Mathlib.Meta.SetNotationForOrder.«binderPred⊇_»,
      `termDepIfThenElse,
      `boolIfThenElse,
      `BigOperators.bigsum,
      `BigOperators.bigprod,
      `BigOperators.bigOpBinders,
      `BigOperators.bigOpBinder,
      `BigOperators.bigOpBinderCollection,
      `BigOperators.bigOpBinderParenthesized,
      `ArithmeticFunction.bigproddvd,
      `Algebra.subalgebra_adjoin,
      `«AddActionHomLocal≺»,
      `«MulSemiringActionHomIdLocal≺»,
      `GeneratedNamespace.«GeneratedActionHomLocal≺»,
      `Batteries.ExtendedBinder.extBinders,
      `Batteries.ExtendedBinder.extBinder,
      `Batteries.ExtendedBinder.extBinderCollection,
      `Batteries.ExtendedBinder.extBinderParenthesized,
      `Lean.Parser.Syntax.unary,
      `Lean.Parser.Syntax.nonReserved,
      `Batteries.Tactic.Alias.alias,
      `Batteries.Tactic.Alias.aliasLR,
      `Batteries.Tactic.Lint.nolint,
      `Batteries.Util.LibraryNote.commandLibrary_note___,
      `Mathlib.Linter.UnusedTactic.«command#allow_unused_tactic!___»,
      `Lean.Parser.Attr.grind!,
      `Lean.Parser.Attr.simple,
      `Lean.Parser.Attr.simps,
      `Lean.Parser.Attr.attrSimps!_,
      `Lean.Parser.Attr.simpsArgsRest,
      `Lean.Parser.Attr.simpsConfig,
      `Lean.Parser.Attr.simpsConfigItem,
      `Lean.Parser.Attr.norm_cast,
      `Lean.Parser.Attr.ext,
      `Lean.Parser.Attr.extIff,
      `Lean.Parser.Attr.higherOrder,
      `Lean.Parser.Attr.grindFwd,
      `Lean.Parser.Attr.grindBwd,
      `Lean.Parser.Attr.grindCases,
      `Lean.Parser.Attr.grindEqBoth,
      `Lean.Attr.coe,
      `Lean.Parser.Attr.instance,
      `Lean.Parser.Attr.class,
      `Lean.deprecated,
      `token.existing,
      `Parser.Attr.functor_norm,
      `Parser.Attr.parity_simps,
      `Parser.Attr.fin_omega,
      `Parser.Attr.enat_to_nat_top,
      `Parser.Attr.enat_to_nat_coe,
      `Parser.Attr.pnat_to_nat_coe,
      `Parser.Attr.nontriviality,
      `Parser.Attr.mfld_simps,
      `Parser.Attr.rclike_simps,
      `Parser.Attr.mon_tauto,
      `Mathlib.Tactic.ToAdditive.to_additive,
      `Mathlib.Tactic.MkIff.mkIff,
      `Mathlib.Tactic.Translate.attrArgs,
      `ArithmeticFunction.attrArith_mult,
      `Parser.Attr.coassoc_simps,
      `Parser.Attr.ghost_simps,
      `Mathlib.Tactic.Translate.bracketedOption,
      `Mathlib.Tactic.Translate.translationHint,
      `Mathlib.Tactic.scopedNS,
      `Mathlib.Tactic.Push.pushAttr,
      `Mathlib.Tactic.GCongr.gcongrAttr,
      `Mathlib.Tactic.Monotonicity.Attr.mono,
      `Mathlib.Tactic.TermCongr.termCongr,
      `Mathlib.PPWithUniv.ppWithUnivAttr,
      `Mathlib.Elab.FastInstance.fastInstance,
      `Mathlib.ProxyType.proxy_equiv,
      `Mathlib.Util.«commandCompile_inductive%_»,
      `Mathlib.Util.«commandCompile_def%_»,
      `Mathlib.GuardExceptions.parseCmd,
      `transImportsStx,
      `aliasIn,
      `commandUnsuppress_compilationIn_,
      `Mathlib.Util.TermReduce.deltaStx,
      `Mathlib.Meta.setBuilder,
      `Set.Mathlib.Meta.setBuilder,
      `Ideal.Submodule.Module.Submodule.Module.Module.Submodule.Submodule.Module.Module.Submodule.Submodule.QuotientTorsion.Ideal.Quotient.AddMonoid.AddSubgroup.torsionByStx,
      `Mathlib.Meta.macroPattSetBuilder,
      `Mathlib.Meta.SetNotationForOrder.«binderPred⊂_»,
      `Mathlib.Notation3.notation3,
      `Mathlib.Notation3.notation3Item,
      `Mathlib.Notation3.identOptScoped,
      `Mathlib.Notation3.prettyPrintOpt,
      `Mathlib.Notation3.foldAction,
      `Mathlib.Notation3.foldKind,
      `LinearAlgebra.Projectivization.termℙ,
      `Qq.matcher,
      `Qq.doElemAssertInstancesCommute,
      `Lean.«doElemTrace[_]__»,
      `term.pseudo.antiquot,
      `Lean.termThrowError__,
      `Lean.Parser.«command__Dsimproc__[_]_(_):=_»,
      `Mathlib.CrossRef.wikidataTag,
      `Mathlib.CrossRef.stacksTag,
      `Mathlib.CrossRef.stacksTagDBStacks,
      `stacksTag,
      `Finsupp.Internal.stxSingle₀,
      `Finsupp.Internal.stxUpdate₀,
      `Finsupp.fun₀,
      `Finsupp.fun₀.matchAlts,
      `Aesop.Frontend.Parser.aesop,
      `Aesop.Frontend.Parser.aesopTactic,
      `Aesop.Frontend.Parser.bool_litTrue,
      `Aesop.Frontend.Parser.bool_litFalse,
      `Aesop.Frontend.Parser.declareRuleSets,
      `Aesop.Frontend.Parser.attr_rules_,
      `Aesop.Frontend.Parser.rule_expr_,
      `Aesop.Frontend.Parser.rule_expr___,
      `Aesop.Frontend.Parser.ruleSetsFeature,
      `Aesop.Frontend.Parser.feature_,
      `Aesop.Frontend.Parser.feature__1,
      `Aesop.Frontend.Parser.feature__2,
      `Aesop.Frontend.Parser.feature__3,
      `Aesop.Frontend.Parser.feature__4,
      `Aesop.Frontend.Parser.«feature(_)»,
      `Aesop.Frontend.Parser.phaseSafe,
      `Aesop.Frontend.Parser.phaseNorm,
      `Aesop.Frontend.Parser.phaseUnsafe,
      `Aesop.Frontend.Parser.builder_nameApply,
      `Aesop.Frontend.Parser.builder_nameCases,
      `Aesop.Frontend.Parser.builder_nameDestruct,
      `Aesop.Frontend.Parser.builder_nameForward,
      `Aesop.Frontend.Parser.builder_nameTactic,
      `Aesop.Frontend.Parser.builder_nameUnfold,
      `Aesop.Frontend.Parser.«builder_option(Index:=[_])»,
      `Aesop.Frontend.Parser.indexing_modeTarget_,
      `Aesop.Frontend.Parser.«priority_%»,
      `Aesop.Frontend.Parser.«priority-_»,
      `measurability,
      `finiteness,
      `eqns,
      `Lean.Parser.Command.binderPredicate,
      `positivity,
      `Mathlib.Meta.Positivity.Meta.Positivity.Tactic.Positivity.positivity,
      `norm_num,
      `rawNatLit,
      `Lean.Parser.Level.hole,
      `Lean.Parser.Level.paren,
      `Lean.Parser.Level.max,
      `Lean.Parser.Tactic.quot,
      `PiNotation.piNotation,
      `prioLow,
      `prioMid,
      `prioHigh,
      `prioDefault,
      `Lean.Parser.precedence,
      `Lean.Parser.Term.declName,
      `precMax,
      `cfcTac,
      `adaptationNoteCmd,
      `Lean.Parser.discrTreeSimpKeyCmd,
      `Lean.Elab.ConfigEval.declareTacticConfig,
      `Lean.Elab.ConfigEval.deriveEvalExprUsingMeta,
      `Lean.Elab.ConfigEval.configEntries,
      `Lean.Elab.ConfigEval.configEntry,
      `Lean.Elab.ConfigEval.configEntryHandler,
      `Lean.Elab.ConfigEval.configEntryHandlerKey,
      `Lean.Elab.ConfigEval.configEntryHandlerKeyPrefix,
      `adaptationNoteTermStx,
      `commandSuppress_compilation,
      `notation_class,
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
      `CategoryTheory.SimplicialObject.Truncated.mkNotation,
      `SimplexCategory.Truncated.mkNotation,
      `TopCat.Presheaf.attrSheaf_restrict,
      `proof_wanted,
      `BigOperators.bigexpect,
      `Std.termF!_,
      `antiquotNestedExpr,
      `precArg,
      `Matrix.vecNotation,
      `Matrix.matrixNotation,
      `PiLp.vecNotation,
      `Lean.Parser.Command.syntaxCat,
      `Lean.Parser.Command.coinductive,
      `Lean.Parser.Command.registerTryTactic,
      `Lean.Parser.Term.doRepeat,
      `Lean.Parser.Term.doBreak,
      `Lean.Parser.Term.doDbgTrace,
      `Lean.Parser.Term.doIdbg,
      `Lean.Parser.Term.doCatchMatch,
      `Lean.termM!_,
      `Mathlib.Meta.FunProp.funPropTacStx,
      `Mathlib.CrossRef.stacksTagDBKerodon,
      `Mathlib.CrossRef.lmfdbTag,
      `Lean.Parser.«command_Dsimproc_decl_(_):=_»,
      `Lean.Parser.Term.withAnonymousAntiquot,
      `Lean.Parser.Term.falseVal,
      `Lean.includeStr,
      `Parser.Attr.zify_simps,
      `attrContinuity
    ]
  for kind in kinds do
    let tree := SyntaxTree.Tree.node (.raw kind) #[]
    assertTrue s!"mathlib low-risk syntax has rule: {kind}"
      (Formatter.LineBreakRules.ruleFor tree).isSome
  let linterItems :=
    SyntaxTree.Tree.node (.raw `null)
      #[.leaf (syntheticAtomToken "linter.one"), .leaf (syntheticAtomToken "linter.two")]
  let linterSetChildren :=
    SyntaxTree.regroupRegisterLinterSetChildren
      #[
        .node (.raw `null) #[],
        .leaf (syntheticAtomToken "register_linter_set"),
        .leaf (syntheticAtomToken "linter.test"),
        .leaf (syntheticAtomToken ":="),
        linterItems
      ]
  assertTrue "register_linter_set list wrapper is flattened" (linterSetChildren.size == 6)
  let linterSetTree :=
    SyntaxTree.Tree.node (.raw `Lean.Linter.«command_Register_linter_set_:=_»)
      linterSetChildren
  match Formatter.LineBreakRules.ruleFor linterSetTree with
  | some rule =>
      let segment := Formatter.LineBreakRules.Segment.ofTree linterSetTree
      assertTrue "register_linter_set item breaks are mandatory"
        (rule.mandatory {} segment)
      assertTrue "register_linter_set breaks before every linter"
        (rule.breakPoints {} segment
          == [{ index := 4, indentLevels := 1 }, { index := 5, indentLevels := 1 }])
  | none =>
      throw <| IO.userError "register_linter_set has no rule"
  let vectorTree :=
    SyntaxTree.Tree.node (.raw `Matrix.vecNotation)
      #[
        .leaf (syntheticAtomToken "!["),
        .leaf (syntheticAtomToken "a"),
        .leaf (syntheticAtomToken ","),
        .leaf (syntheticAtomToken "b"),
        .leaf (syntheticAtomToken "]")
      ]
  match Formatter.LineBreakRules.ruleFor vectorTree with
  | some rule =>
      assertEq "matrix vector notation uses array rule" "array" rule.name
      let vectorSegment := Formatter.LineBreakRules.Segment.ofTree vectorTree
      assertTrue "matrix vector notation has item and close breaks"
        (rule.breakPoints {} vectorSegment
          == [
            { index := 1, indentLevels := 1 },
            { index := 3, indentLevels := 1 },
            { index := 4, indentLevels := 0 }
          ])
  | none => throw <| IO.userError "matrix vector notation has no rule"
  let matrixTree :=
    SyntaxTree.regroupTree
    <| SyntaxTree.Tree.node (.raw `Matrix.matrixNotation)
        #[
          .leaf (syntheticAtomToken "!!["),
          .node (.raw `null)
            #[
              .node (.raw `null)
                #[
                  .leaf (syntheticAtomToken "a"),
                  .leaf (syntheticAtomToken ","),
                  .leaf (syntheticAtomToken "b")
                ],
              .leaf (syntheticAtomToken ";"),
              .node (.raw `null)
                #[
                  .leaf (syntheticAtomToken "c"),
                  .leaf (syntheticAtomToken ","),
                  .leaf (syntheticAtomToken "d")
                ]
            ],
          .leaf (syntheticAtomToken "]")
        ]
  match matrixTree, Formatter.LineBreakRules.ruleFor matrixTree with
  | .node _ children, some rule =>
      assertTrue "matrix notation rows and columns are flattened for layout"
        (children.size == 9)
      assertEq "matrix notation uses its flowing collection rule"
        "matrixNotation" rule.name
      let matrixSegment := Formatter.LineBreakRules.Segment.ofTree matrixTree
      assertTrue "matrix notation breaks before entries and the close delimiter"
        (rule.breakPoints {} matrixSegment
          == [
            { index := 1, indentLevels := 1 },
            { index := 3, indentLevels := 1 },
            { index := 5, indentLevels := 1 },
            { index := 7, indentLevels := 1 },
            { index := 8, indentLevels := 0 }
          ])
  | _, _ => throw <| IO.userError "matrix notation has no regrouped rule"
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
  let bracketedSimprocTree :=
    SyntaxTree.Tree.node (.raw `Lean.Parser.«command__Simproc__[_]_(_):=_») #[]
  assertTrue "bracketed simproc declarations keep original formatting"
    (Formatter.shouldEmitOriginalTree bracketedSimprocTree)
  let libraryNoteTree :=
    SyntaxTree.Tree.node (.raw `Batteries.Util.LibraryNote.«commandLibrary_note___») #[]
  assertTrue "Batteries library notes keep original formatting"
    (Formatter.shouldEmitOriginalTree libraryNoteTree)
  let jsxTree :=
    SyntaxTree.Tree.node (.raw `ProofWidgets.Jsx.«proofWidgetsJsxElement<__>_</_>») #[]
  assertTrue "ProofWidgets JSX keeps original formatting"
    (Formatter.shouldEmitOriginalTree jsxTree)
  assertTrue "ProofWidgets JSX is skipped by missing-rule reporting"
    (Formatter.Diagnostics.missingRuleOccurrences "" none jsxTree).isEmpty
  let jsonTree := SyntaxTree.Tree.node (.raw `Lean.Json.«json{_}») #[]
  assertTrue "Lean JSON syntax keeps original formatting"
    (Formatter.shouldEmitOriginalTree jsonTree)
  assertTrue "Lean JSON syntax is skipped by missing-rule reporting"
    (Formatter.Diagnostics.missingRuleOccurrences "" none jsonTree).isEmpty

def assertMissingRuleCheckUsesDispatch
    (env : Lean.Environment) (cache : LeanFmt.Driver.EnvironmentCache)
    : IO Unit := do
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
  let projectImports ←
    LeanFmt.Driver.importsForSource
      "import LeanFmt.Tests.ProjectSyntax\n" "project-syntax-import.lean"
  let projectEnv ← cache.environmentForImports projectImports
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
  let formatted ← Formatter.formatSourceWithEnv env source "syntax-declaration-rules.lean"
  assertTextContains "syntax separator stays tight" formatted "term,*"

def assertElaborationSyntaxHasRules (env : Lean.Environment) : IO Unit := do
  let source :=
    "open Lean Parser Term\n"
    ++ "\n"
    ++ "meta def parserExample : Parser :=\n"
    ++ "  leading_parser withPosition <| ident\n"
    ++ "\n"
    ++ "elab \"identity% \" t:term : term => do\n"
    ++ "  let declarationName := ``Nat.succ\n"
    ++ "  return t\n"
    ++ "\n"
    ++ "initialize registerTraceClass `LeanFmt.Tests\n"
    ++ "\n"
    ++ "run_cmd Lean.Elab.Command.liftTermElabM do\n"
    ++ "  pure ()\n"
  let formatted ← Formatter.formatSourceWithEnv env source "elaboration-syntax-rules.lean"
  assertTrue "elaboration syntax formatting preserves code"
    (← codePreservedIgnoringWhitespace env source formatted)
  assertTextContains "elaborator declarations keep their source layout"
    formatted
    ("elab \"identity% \" t:term : term => do\n"
      ++ "  let declarationName := ``Nat.succ\n"
      ++ "  return t\n")
  let moduleTree ←
    SyntaxTree.parseModuleStringWithEnv env formatted
      "elaboration-syntax-rules-formatted.lean"
  assertTrue "elaboration syntax has complete rule coverage"
    (Formatter.Diagnostics.missingRuleOccurrencesForModule moduleTree).isEmpty
  let formattedAgain ←
    Formatter.formatSourceWithEnv env formatted "elaboration-syntax-rules-idempotent.lean"
  assertEq "elaboration syntax formatting is idempotent" formatted formattedAgain

def assertMatchExprAlternativesStartOnNewLines (env : Lean.Environment) : IO Unit := do
  let source :=
    "def inspectExpr (e : Lean.Expr) : Lean.Meta.MetaM Lean.Expr := do\n"
    ++ "  match_expr e with\n"
    ++ "  | Nat.succ n =>\n"
    ++ "    if true then\n"
    ++ "      return n\n"
    ++ "    else return e\n"
    ++ "  | Nat.zero =>\n"
    ++ "    return e\n"
    ++ "  | _ => return e\n"
  let formatted ←
    Formatter.formatSourceWithEnv env source "match-expr-alternative-breaks.lean"
  assertTextContains "match_expr alternatives keep a leading line break"
    formatted "\n  | Nat.zero =>"
  assertTextLacks "match_expr alternatives do not join the previous return"
    formatted "return e | Nat.zero"
  let formattedAgain ←
    Formatter.formatSourceWithEnv env formatted
      "match-expr-alternative-breaks-idempotent.lean"
  assertEq "match_expr alternative formatting is idempotent" formatted formattedAgain
  let attachedDoSource :=
    "def inspectAttachedDo (e : Lean.Expr) : Lean.Meta.MetaM Lean.Expr := do\n"
    ++ "  match e with\n"
    ++ "  | .app f _ => do\n"
    ++ "    if true then\n"
    ++ "      return f\n"
    ++ "    else return e\n"
    ++ "  | _ => return e\n"
  let attachedDoFormatted ←
    Formatter.formatSourceWithEnv env attachedDoSource "match-attached-do-base.lean"
  assertTextContains "attached do keeps the match-arm base"
    attachedDoFormatted
    ("  | .app f _ => do\n"
      ++ "      if true then\n"
      ++ "        return f\n"
      ++ "      else\n"
      ++ "        return e\n")
  assertTextLacks "attached do body does not inherit the pattern end column"
    attachedDoFormatted "\n                  if true then"

def assertApplicationFitCountsFromSuffix (env : Lean.Environment) : IO Unit := do
  let source :=
    "theorem showLongApplication : True :=\n"
    ++ "  show ExtremelyLongPredicateNameForApplicationFit firstArgumentWithLength\n"
    ++ "    (fun y => veryLongTransformName (anotherLongTransformName y) (thirdLongArgumentName y)) s x from\n"
    ++ "  proofTerm\n"
  let formatted ←
    Formatter.formatSourceWithEnv env source "show-application-from-suffix.lean"
      { lineWidth := 100 }
  assertTrue "show application counts from suffix in line fit"
    (Formatter.linesFit formatted 100)
  assertTextContains "show application breaks before overflowing final argument"
    formatted "\n        x from"

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

def assertSyntaxAuthoringDefinitionPreservesCode (env : Lean.Environment) : IO Unit := do
  let source :=
    "syntax \"customTerm\" : term\n"
    ++ "def quotedSyntax : Lean.Elab.Term.TermElabM Lean.Syntax := do\n"
    ++ "  `(customTerm)\n"
  let result ←
    Formatter.formatSourceWithEnvDetailed env source "syntax-authoring-definition.lean"
  assertTrue "syntax authoring definition does not fall back" (!result.fellBack)
  assertTrue "syntax authoring definition preserves code"
    (← codePreservedIgnoringWhitespace env source result.formatted)

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

def assertIgnoredRegionsPreserveSourceLines (env : Lean.Environment) : IO Unit := do
  let source :=
    "def before:Nat:=1\n"
    ++ "\n"
    ++ "-- leanfmt: off\n"
    ++ "def ignored   :   Nat:=\n"
    ++ "       2\n"
    ++ "-- leanfmt: on\n"
    ++ "\n"
    ++ "def after:Nat:=3\n"
  let expected :=
    "def before:Nat:=1\n"
    ++ "-- leanfmt: off\n"
    ++ "def ignored   :   Nat:=\n"
    ++ "       2\n"
    ++ "-- leanfmt: on\n"
    ++ "def after:Nat:=3\n"
  let formatted ← Formatter.formatSourceWithEnv env source "ignored-region.lean"
  assertEq "ignored region preserves source lines while formatting outside"
    expected formatted
  let formattedAgain ← Formatter.formatSourceWithEnv env formatted "ignored-region.lean"
  assertEq "ignored region formatting is idempotent" formatted formattedAgain

def assertIgnoredRegionMayContinueToEnd (env : Lean.Environment) : IO Unit := do
  let source :=
    "def before:Nat:=1\n"
    ++ "-- leanfmt: off\n"
    ++ "def ignored   :   Nat:=\n"
    ++ "       2\n"
  let expected :=
    "def before:Nat:=1\n"
    ++ "-- leanfmt: off\n"
    ++ "def ignored   :   Nat:=\n"
    ++ "       2\n"
  let formatted ← Formatter.formatSourceWithEnv env source "ignored-region-to-end.lean"
  assertEq "unterminated ignored region preserves to end of file" expected formatted

def assertIgnoreNextPreservesNextCommand (env : Lean.Environment) : IO Unit := do
  let source :=
    "-- leanfmt: off next\n"
    ++ "def kept   :   Nat:=\n"
    ++ "       1\n"
    ++ "\n"
    ++ "def after:Nat:=2\n"
  let expected :=
    "-- leanfmt: off next\n"
    ++ "def kept   :   Nat:=\n"
    ++ "       1\n"
    ++ "\n"
    ++ "def after:Nat:=2\n"
  let formatted ← Formatter.formatSourceWithEnv env source "ignored-next-command.lean"
  assertEq "ignore next preserves only the next command" expected formatted
  let formattedAgain ←
    Formatter.formatSourceWithEnv env formatted "ignored-next-command.lean"
  assertEq "ignore next command formatting is idempotent" formatted formattedAgain

def assertIgnoreNextPreservesAttributedCommand (env : Lean.Environment) : IO Unit := do
  let source :=
    "-- leanfmt: off next\n"
    ++ "@[simp]\n"
    ++ "theorem kept   :   True:=by\n"
    ++ "       trivial\n"
    ++ "\n"
    ++ "def after:Nat:=2\n"
  let expected :=
    "-- leanfmt: off next\n"
    ++ "@[simp]\n"
    ++ "theorem kept   :   True:=by\n"
    ++ "       trivial\n"
    ++ "\n"
    ++ "def after:Nat:=2\n"
  let formatted ←
    Formatter.formatSourceWithEnv env source "ignored-next-attributed-command.lean"
  assertEq "ignore next preserves an attributed command" expected formatted

def assertIgnoreNextPreservesNestedTerm (env : Lean.Environment) : IO Unit := do
  let source :=
    "def kept\n"
    ++ "    : Nat → Nat :=\n"
    ++ "  -- leanfmt: off next\n"
    ++ "  fun i =>\n"
    ++ "    if i = 0 then 1\n"
    ++ "    else          2\n"
    ++ "\n"
    ++ "def after:Nat:=2\n"
  let expected :=
    "def kept : Nat → Nat :=\n"
    ++ "  -- leanfmt: off next\n"
    ++ "  fun i =>\n"
    ++ "    if i = 0 then 1\n"
    ++ "    else          2\n"
    ++ "\n"
    ++ "def after:Nat:=2\n"
  let formatted ← Formatter.formatSourceWithEnv env source "ignored-next-term.lean"
  assertEq "ignore next preserves a nested term and its command boundaries"
    expected formatted
  let formattedAgain ←
    Formatter.formatSourceWithEnv env formatted "ignored-next-term.lean"
  assertEq "nested ignore next formatting is idempotent" formatted formattedAgain

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
  assertUnifHintChildrenRegrouped
  assertPreservationDetectsSyntaxChange env
  assertOverlappingQuotationTokensRemoved env
  assertTacticQuotationAntiquotationPreserved env
  assertFullyQualifiedQuotedNamesStayTight env
  assertOverlappingEmptySyntaxTokensRemoved env
  assertGroupedApplication env
  assertGroupedInfixChain env

def runBasicFormattingTests (env : Lean.Environment) : IO Unit := do
  assertSafeArrayIndexKeepsPostfixQuestion env
  assertGetElemBracketStaysAttachedAcrossWrap env
  assertPostfixSuperscriptSpacingPreservesParse env
  assertBlockCommentInternalWhitespacePreservedByFormatting env
  assertIndentedCommentTriviaDoesNotPadBlankLines
  assertAtomicTokenRetainsFittingSourceColumn env
  assertDoBodyRetainsSourceLayoutToAvoidOverflow env
  assertRegisterOptionValueUsesDeclarationLayout env
  assertAliasCommandRetainsSourceLayout env
  assertModuleDocInternalBlankLinesPreservedByFormatting env
  assertCustomNotationBracketSpacing
  assertOperatorLikeModifierTokenPreservesParse env
  assertSetOptionInBreaksAfterIn env
  assertDocumentedTopLevelDeclarationKeepsBaseIndent env
  assertModifiedTopLevelCommandsUseLineBase env
  assertCommandInWrapperPreservesBreakAfterIn env
  assertStackedCommandInWrappersBreakBeforeDeclaration env
  assertLeadingDotPatternConstructorsStayTight env
  assertFormatterConvergencePassLimit
  assertFormatterFallbackResultIsObservable env
  assertLayoutSensitiveTermsRemainParseableAndIdempotent env
  assertLineWidthOptionAffectsFormatting env
  assertHardWhitespaceFormatting env
  assertConfigEntriesStaySeparated env
  assertImportsStayOnSeparateLines env
  assertModuleHeaderGroupsUseBlankLines env
  assertMultilineTopLevelDeclarationsUseBlankLines env
  assertLongImportStaysOnOneLine env
  assertNamespaceCommandsStayOnSeparateLines env
  assertOpenCommandListBreaksFromOpenColumn env
  assertCommentsDoNotBlockFormatting env
  assertLeadingCommentsPreserved env
  assertTrailingLineCommentPreserved env
  assertAnonymousConstructorAfterListKeepsSpace env
  assertAttributeDeclarationPreservesSourceBreak env
  assertAttributesFlowBeforeDeclarations env
  assertWhereDeclarationAttributeBreaksBeforeDeclaration env
  assertEquationWhereUsesDeclarationBase env
  assertSingleLineOriginalAttributeSyntaxFitsInline env
  assertCommandAttributeBracketPayloadStaysAttached env
  assertPrivateTheoremModifierStaysOnHeader env
  assertDoBlockPreservesBodyBreak env
  assertDoMatchAlternativesAlignWithMatch env
  assertDoBlockPreservesStatementBreaks env
  assertDoReassignArrowHasRule env
  assertShowAndDoWrapperRules env
  assertProjectionChainDoesNotBreakBeforeDot env
  assertPipeProjectionKeepsTightDot env
  assertLongPipeProjectionKeepsTightDot env
  assertPipeProjectionInDeclarationTypeIndentsContinuation env
  assertPipeProjectionDoesNotBreakAfterDot env
  assertMatchAltProofRhsKeepsByOnArrowLine env
  assertRecordBraceSpacing env
  assertDerivingStaysOnOwnLine env
  assertDefinitionDerivingStaysOnOwnLine env
  assertLongDerivingClauseFlowsClasses env
  assertLongDerivingInstanceFlowsClasses env
  assertMatchMotiveUsesTransparentRule env
  assertStructureBreaksTopLevelFields env
  assertPrivateStructureFieldsUseCommandBase env
  assertStructureFieldProofBreaksAfterAssignment env
  assertStructureInstanceMethodBindersFlow env
  assertBinderDefaultValueUsesBinderBase env
  assertParenthesizedStructureDefaultUsesFieldBase env
  assertAbbrevSourceBreakAfterAssign env
  assertMatchArmKeepsDoOnArrowLine env
  assertWhereFormattingKeepsSuffix env
  assertStructureValueWhereFormattingKeepsSuffix env
  assertWhereFinallyKeepsHeaderAndProofBody env
  assertProofBodyUntouched env
  assertMovedProofBodiesKeepRelativeIndentation env
  assertMovedInlineProofBodiesRemainParseable env
  assertShowProofTermUntouched env
  assertTheoremTermProofBodyUntouched env
  assertTheoremEquationProofBodyUntouched env
  assertInstanceEquationArmsUseDeclarationBase env
  assertDefinitionContainingProofUntouched env
  assertInstanceContainingProofUntouched env
  assertTerminationProofSuffixUntouched env
  assertTerminationProofSuffixDoesNotAccumulateIndent env
  assertTerminationByBreakPriority env
  assertTerminationClausesUseDeclarationBase env
  assertDocumentedMutualCommandsKeepBase env
  assertMovedDocumentedDoLetRecRebasesCommentedArms env
  assertBasicDeclarationBreak env
  assertTopLevelAnnotationsBreakConsistently env
  assertDeclarationValueInfixBreaksAfterAssign env
  assertLongDeclarationDirectValueBreaksAfterAssign env
  assertDeclarationProofValueBreaksAfterAssignWhenSignatureCannotFit env
  assertDeclarationProofIntroducerStaysWithAssignment env
  assertDeclarationValueWithNestedProofBreaksAfterAssignment env
  assertTheoremDirectValueBreaksBeforeSignatureChildren env
  assertDeclarationWhereSuffixCountsForSignatureFit env
  assertDeclarationValueKeepsAttachedByBody env
  assertDeclarationValueKeepsAttachedDoBody env
  assertAttachedDoInAssignmentInfixUsesDeclarationBase env
  assertProofValuesRemainLayoutIslands env
  assertOriginalLayoutValueHonorsDeclarationBreak env
  assertCalcLayoutIslandAfterNestedInfix env
  assertHaveTermFormatting env
  assertHaveProofAfterInfixPreservesLayout env
  assertAbsoluteValueDelimitersStayAttached env
  assertSymmetricDelimitersStayAttachedAcrossPasses env
  assertGeneratedPostfixMarkersStayAttached env
  assertNotExistsIdentifiersFlow env
  assertSignatureParametersUseLeadingSourceBreakAfterFlatFails env
  assertDefinitionSourceBreakAfterAssignOverridesFlat env

def runExpressionAndRendererTests (env : Lean.Environment) : IO Unit := do
  assertSelfFormattingLetAndArrayRegressions env
  assertCliSelfFormattingRegressions env
  assertSelfFormattingRulePriorities env
  assertApplicationFlow env
  assertApplicationFitsBeforeSourceBreaks env
  assertNestedApplicationHonorsSourceBreaks env
  assertApplicationCommentBreakAvoidsOverflowAfterOuterShift env
  assertApplicationArgumentUsesHeadAnchorAfterTypeBreak env
  assertLetExpressionKeepsBodyBreak env
  assertLetIExpressionKeepsBodyBreak env
  assertLetExpressionBlocksFlatRendering env
  assertParenthesizedLetIKeepsTightOpeningDelimiter env
  assertBinderLetIDoesNotPadAfterColon env
  assertParenthesizedLetRhsIndentUnderImplication env
  assertParenthesizedLetAlignmentFollowsBodyPrecedence env
  assertParenthesizedLetWithMatchBodyKeepsTightOpening env
  assertParenthesizedLetUsesProjectSyntaxPrecedence env
  assertTheoremParenthesizedLetKeepsValueSuffix env
  assertLetBodyAfterInfixClosesLetLayout env
  assertDeclarationTypeBreak env
  assertImplicitBinderPreservesTightBraces env
  assertExplicitBinderTypeBreak env
  assertGroupedBinderIdentifiersFlow env
  assertSignatureParametersFitBeforeSourceBreaks env
  assertSignatureParametersStayOnHeaderWhenTheyFit env
  assertSignatureParameterSourceBreakFallback env
  assertVariableBinderSequenceFlows env
  assertVariableInstanceBinderAvoidsBracketOnlyLines env
  assertCommandBinderSequencesFlow env
  assertMutualEquationArmIndent env
  assertMutualSingleLineParameterReturnIndent env
  assertReturnTypeInfixIndent env
  assertReturnTypeArrowFlows env
  assertLogicalArrowBreaksBalanced env
  assertChildFitCountsParentSuffix env
  assertNestedChildFitCountsInfixSuffix env
  assertNestedChildFitCountsProjectionMemberSuffix env
  assertLineFitCountsTrailingComment env
  assertColumnIndentationIsConservative
  assertCurrentLineFitChecksCompletedLines
  assertMovedProofWidgetsJsxUsesPendingIndent
  assertSegmentBaseUsesRenderedStartColumn
  assertListApplicationColumnIndent env
  assertListApplicationSourceBreakIndent env
  assertSingletonArrayKeepsBodyBase env
  assertMultiItemArrayBreaksBalanced env
  assertListLikeCollectionsBreakBalanced env
  assertOffColumnArrayRoundsOneLevel env
  assertInstanceWhereStaysWithHeader env
  assertInfixLeftDepth env
  assertInfixAlternativeSequenceFlows env
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
  assertElseIfChainBreaksThenBranchesTogether env
  assertTermMatchAlternativesStayOnOwnLines env
  assertLetMatchAlternativesAlign env
  assertMatchArmPreservesSourceBreakBeforeShortRhs env
  assertIfThenElseBreaksBalanced env
  assertParenthesizedIfKeepsTightHeadAndAlignedBranches env
  assertMatchArmRhsIndent env
  assertMatchPeerBreakConsistency env
  assertMatchDiscriminantApplicationIndent env
  assertNestedTermMatchAlternativesAlign env
  assertNestedMatchAfterLambdaAlignsWithMatch env
  assertPrefixedMatchAlternativesAlignWithMatch env
  assertLambdaBodyUsesOperandAnchor env
  assertLambdaBinderSequenceBreaksBetweenBinders env
  assertQuantifierBreaksAfterComma env
  assertBreakNeverPrecedesTrailingSeparator env
  assertQuantifierIdentifierSequenceFlows env
  assertArrowQuantifierKeepsQuantifierOnArrowLine env
  assertArrowMatchKeepsMatchOnArrowLine env
  assertArrowMatchInMatchAltIdempotent env
  assertQuantifierBinderSequenceBreaksBetweenBinders env

def runCollectionAndDeclarationTests (env : Lean.Environment) : IO Unit := do
  assertInductiveConstructorIndentation env
  assertClassInductiveAlternativesStaySeparated env
  assertConstructorBinderContinuesFromUnbrokenPrefix env
  assertStructureFieldsBreakMandatory env
  assertStructureFieldTypeBreakIndentation env
  assertStructureExtendsBreaksBeforeWhereFields env
  assertShortStructureExtendsHeaderStaysFlat env
  assertStructureExtendsDoesNotIndentFollowingCommand env
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
  Lean.initSearchPath (← Lean.findSysroot)
  let entries ← IO.mkRef []
  let cache : LeanFmt.Driver.EnvironmentCache :=
    { default := env, maxEntries := 1, entries }
  assertCliParsing
  assertEnvironmentCacheBound env
  assertDefaultEnvironmentPartition env
  assertWorkersUseInputLakeRoot
  assertImportFilesGroupByHeader
  assertImportFilesGroupByLakeSetupImportArtifacts
  assertImportFilesUseDefaultAggregatorAsEnvironmentCandidate
  assertRecursiveWorkerChecksTargetToolchain
  assertFormattingExceptionChecks env
  assertCliChecksStillFormatUnlessCheck env cache
  assertCliFormatsDirectory env cache
  assertCliFormatsDirectoryRecursively env cache
  assertCliSkipsHiddenPathsByDefault
  assertCliLoadsImportedSyntax cache
  assertFmtExecutableConfigured
  assertRendererTraceIncludesPathAndState env
  assertCliFixtureUpdate env
  assertFormatterArchitecture
  assertDeclarationRuleTransparent
  assertLakeDslFormatting
  assertMathlibLowRiskSyntaxKindsHaveRules
  assertMissingRuleCheckUsesDispatch env cache
  assertCheckCommandHasRule env
  assertGuardMsgsCommandUsesCommandInLayout env
  assertBinderTacticProofBodyHasNoMissingRules env
  assertInstanceValueInheritsDeclarationBase env
  assertSufficesBodyBreaksAfterFromProof env
  assertSyntaxDeclarationsHaveRules env
  assertElaborationSyntaxHasRules env
  assertMatchExprAlternativesStartOnNewLines env
  assertApplicationFitCountsFromSuffix env
  assertParserStateUpdatesAfterSyntaxCommands env
  assertSyntaxAuthoringDefinitionPreservesCode env
  assertCustomBracedTermSyntaxKeepsNestedSourceLayout env
  assertPrefixedTermWrappersHaveRules env
  assertIgnoredRegionsPreserveSourceLines env
  assertIgnoredRegionMayContinueToEnd env
  assertIgnoreNextPreservesNextCommand env
  assertIgnoreNextPreservesAttributedCommand env
  assertIgnoreNextPreservesNestedTerm env
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
