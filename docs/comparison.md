# Comparison with Lean style guides and pretty-lean

This report compares LeanFmt with:

- the [Lean 4 standard-library style guide][lean-style];
- the [Lean community library style guide][community-style];
- [pretty-lean][pretty-lean], a Lean compiler fork with an integrated formatter.

LeanFmt's current normative style remains [design.md](design.md), and its implementation
model is documented in [architecture.md](architecture.md). This report is comparative;
it does not override either document.

The comparison concerns their current documented behavior and implementation. The
two style guides are policies for human contributors, not formatter specifications. The
first applies to Lean's standard library; the community guide describes conventions used
by mathlib and related community libraries. pretty-lean is an experimental implementation
rather than an established style standard. Its checked-in tests are therefore treated as
evidence of current behavior, not as recommendations.

## Executive summary

LeanFmt occupies a distinct point in the design space:

- It is a standalone, project-usable formatter rather than a compiler fork.
- It preserves source tokens, token order, comments, and proof regions instead of
  reconstructing Lean code from a smaller semantic AST.
- It chooses one deterministic layout where the style guides intentionally allow human
  judgement.
- Its leading-operator layout deliberately departs from both documented styles.
- It avoids the toolchain replacement required by pretty-lean.
- It does not yet offer pretty-lean's editor integration or range formatting.

The strongest ideas to borrow are not wholesale formatting styles. They are
pretty-lean's parser-aware extensibility, editor workflow, and check mode; the style
guides' separation between mechanical layout and broader source policy; the community
guide's concrete continuation and proof-layout examples; and Lean's generic
parser-formatter registry. LeanFmt's losslessness, proof preservation, leading operators,
tail indentation, and diagnostic checks should remain defining features.

## At a glance

| Dimension | Standard-library guide | Community guide | LeanFmt | pretty-lean |
| --- | --- | --- | --- | --- |
| Nature | Human policy for Lean's standard library | Human policy for community libraries | Standalone formatter and library | Fork of the Lean compiler and language server |
| Layout model | Several layouts are often permitted | Concrete conventions, still guided by readability | Syntax rules plus a lossless tree and stateful renderer | Lean parser formatters produce `Std.Format` documents |
| Parsing context | Not applicable | Not applicable | Processes imports to load project syntax | Processes the file header; formatting requires parsing, not elaboration |
| Indentation | Two spaces; declaration-header continuations use four | Two spaces; multiline theorem statements use four | Two spaces | Lean `Format` default of two spaces |
| Line width | No fixed limit | At most 100 characters | 90 characters | Lean `Format` default of 120, configurable through options |
| Infix wrapping | Operator ends the preceding line | Operator ends the preceding line | Operator begins the continuation line | Parser pretty-printing places an operator at the preceding line end in current tests |
| Comments | Specifies documentation style and file policy | Specifies headers, module docs, and declaration docs | Preserves comment contents and reindents surrounding trivia | Retains source gaps, but current tests show comment text can be normalized |
| Proofs | Gives semantic and tactical style advice | Prefers readable tactic and calculation layouts | Preserves proof subtrees | Reformats tactic syntax |
| Unknown/custom syntax | Requires public syntax policy but says nothing about formatter fallback | Not addressed as a formatting mechanism | Keeps tokens, uses generic layout, and reports missing rules | Parser authors can register or synthesize formatters with their syntax |
| CLI/CI | Not applicable | Linters and human review complement the guide | In-place formatting, recursive discovery, check mode, and diagnostic checks | `lake format`, `lake fmt`, `lean --format`, and `--format-check`; CLI is marked WIP |
| Safety checks | Review by contributors | Review and library linters | Code preservation, overflow, missing rules, convergence, and optional idempotency | Per-command fallback when pretty-printing fails; check mode detects changes |

## Target-by-target formatting comparison

The examples below put LeanFmt first and the comparison target second. Examples for the
official guide show a layout that the guide requires or explicitly permits. Examples for
pretty-lean are based on its implementation and checked-in fixtures.

### Lean standard-library style guide

LeanFmt shares the [official guide's][lean-style] basic two-space indentation,
four-space declaration-header continuation, argument-boundary application wrapping,
match-arm layout, `where`/termination/`deriving` bases, `do` attachment, and multiline
structure shape. The following designs differ.

#### Infix operators begin versus end continuation lines

LeanFmt puts each operator at the beginning of its continuation. The operators form a
vertical spine:

```lean
firstCondition
&& secondCondition
&& thirdCondition
```

The official guide requires the operator at the end of the preceding line:

```lean
firstCondition &&
  secondCondition &&
  thirdCondition
```

LeanFmt's choice creates the need for tail indentation: a multiline non-final operand
must move inward far enough that its internal lines cannot be confused with the next
operator. This is a defining difference, not a compatibility bug.

#### Wrapped declaration type colons

LeanFmt begins a continuation line with the declaration's type colon:

```lean
def lookupVariableValue? (variableValues : VariableValues) (name : Name)
    : Option InputValue :=
  body
```

The official guide forbids a declaration colon at the beginning of a line. A compatible
layout keeps it after the parameters:

```lean
def lookupVariableValue? (variableValues : VariableValues) (name : Name) :
    Option InputValue :=
  body
```

LeanFmt makes the return type a visually distinct header component. The difference
should remain covered by a focused test rather than emerge accidentally from fitting.

#### Attribute placement

LeanFmt keeps a fitting attribute and declaration together when the source does:

```lean
@[simp] theorem eraseP_nil : [].eraseP p = [] := rfl
```

It preserves a source break between them, and it breaks after the attribute when the
declaration itself must become multiline:

```lean
@[simp]
theorem eraseP_cons (a : α) (l : List α)
    : (a :: l).eraseP p = conditionalResult := by
  proof
```

The official guide permits both placements. LeanFmt is intentionally source-sensitive at
this boundary rather than selecting only one of them.

#### Multiline collections

LeanFmt breaks a multiline collection as one balanced unit:

```lean
[
  firstLongItem,
  secondLongItem,
  thirdLongItem
]
```

The official guide permits alignment under the first item instead:

```lean
[firstLongItem,
 secondLongItem,
 thirdLongItem]
```

It also permits ordinary two-space continuation indentation. LeanFmt deliberately
chooses one balanced form so opening, item, and closing breaks cannot drift apart.

#### Flat structure-instance spacing

LeanFmt preserves tight flat structure braces when the source used them:

```lean
def response := {data := .null, errors := []}
```

The official standard-library style uses spaces inside structure-instance braces:

```lean
def response := { data := .null, errors := [] }
```

LeanFmt also preserves the spaced form when it is present. It is conservative here
rather than fully canonical.

#### Notation spelling

LeanFmt preserves the source lexemes, including an ASCII arrow:

```lean
def applyTwice : (Nat -> Nat) -> Nat -> Nat :=
  body
```

The official guide generally prefers available Unicode notation:

```lean
def applyTwice : (Nat → Nat) → Nat → Nat :=
  body
```

Changing notation is outside LeanFmt's whitespace-only contract. The same principle
applies to lambda spelling and proof style.

#### Human policy without a formatter equivalent

The guide also covers copyright headers, module documentation, documentation mood,
public-syntax review, and proof-engineering practices. These are editorial or semantic
policies, not alternate whitespace layouts. LeanFmt appropriately leaves them to linters
and reviewers.

### Lean community library style guide

The [Lean community guide][community-style] is more expansive than the standard-library
guide. It combines whitespace conventions with library organization, naming, Unicode,
documentation, statement design, proof style, and performance advice. It explicitly
presents these as guidelines rather than rigid rules. LeanFmt overlaps with its
mechanical layout subset while leaving editorial and semantic choices to authors,
linters, and review.

#### Default line width

LeanFmt uses 90 columns by default, so a line in the guide's 91–100-column allowance can
wrap:

```lean
def result :=
  resolveFieldWithValidatedArguments schema parentType sourceValue fieldDefinition
```

The community guide permits lines up to 100 characters, so the same expression may stay
on one line:

```lean
def result := resolveFieldWithValidatedArguments schema parentType sourceValue fieldDefinition
```

The difference is configurable rather than structural: a community project can pass
`--line-width 100`. LeanFmt should retain its own default instead of treating the
community limit as universal.

#### Leading versus trailing infix operators

LeanFmt begins continuation lines with infix operators:

```lean
firstCondition
&& secondCondition
&& thirdCondition
```

The community guide asks that an infix operator remain before the line break:

```lean
firstCondition &&
  secondCondition &&
  thirdCondition
```

This is the same intentional difference as with the standard-library guide. Adopting the
community direction would remove the motivation for some tail indentation, but would
also discard LeanFmt's vertical operator spine and its existing logical layout.

#### Declaration statements and proof indentation

LeanFmt places a wrapped declaration colon at the beginning of a header component and
uses leading operators in the result type:

```lean
theorem resolvesField (schema : Schema) (field : Field)
    : FieldIsDefined schema field
      → ArgumentsAreValid schema field
      → ResolutionSucceeds schema field := by
  proof
```

The community guide keeps the colon and operators before their line breaks. It indents a
multiline theorem statement by four spaces while keeping the proof only two spaces in
from the declaration:

```lean
theorem resolvesField (schema : Schema) (field : Field) :
    FieldIsDefined schema field →
    ArgumentsAreValid schema field →
    ResolutionSucceeds schema field := by
  proof
```

The two styles agree that `by` should remain attached to the preceding statement and
that the proof has a stable two-space base. Their difference is how the statement itself
communicates continuation.

#### Balanced collections versus argument alignment

LeanFmt gives a multiline anonymous constructor balanced delimiters and one item per
line:

```lean
theorem result : (P → Q) ∧ (R → S) :=
  ⟨
    fun h => firstProof h,
    fun h => secondProof h
  ⟩
```

The community guide gives an example in which constructor arguments align beneath the
first argument and the delimiters remain attached:

```lean
theorem result : (P → Q) ∧ (R → S) :=
  ⟨fun h => firstProof h,
   fun h => secondProof h⟩
```

The community form is compact and preserves horizontal alignment. LeanFmt's balanced
form scales more uniformly when either item becomes multiline and avoids using the first
item's starting column as a lasting indentation anchor.

#### Proof source policy versus proof preservation

LeanFmt deliberately preserves the contents of a proof subtree, including a short tactic
sequence written on one line:

```lean
example : Goal := by
  rw [h]; exact result
```

The community guide permits compact tactic sequences in limited cases but generally
prefers one tactic invocation per line:

```lean
example : Goal := by
  rw [h]
  exact result
```

Likewise, the guide describes alignment alternatives for `calc`, focusing dots, named
cases, and when to use term or tactic mode. These are valuable authoring conventions,
but applying them mechanically would require LeanFmt to take ownership of proof layout.
That would conflict with its current conservative proof-preservation boundary.

#### Source policy outside formatting

The community guide also recommends explicit binder and return types, hypotheses to the
left of the declaration colon, `where` syntax for instances, preferred Unicode notation,
module headers and docstrings, declaration docstrings, naming conventions, and proof or
API design practices. These recommendations may require changing syntax or meaning; they
belong in linters, editor assistance, and review rather than LeanFmt's whitespace rules.

The immediate lesson for LeanFmt is narrower: document its intentional leading-operator,
wrapped-colon, balanced-delimiter, width, and proof-preservation differences clearly.
The guide is also a strong source of corpus examples for compatibility tests, even when
LeanFmt deliberately produces a different canonical layout.

### pretty-lean

[pretty-lean][pretty-lean] uses Lean's registered parser formatters and reconstructs
commands as `Std.Format` documents. It therefore formats more of the syntax—including
proofs—rather than preserving selected source regions. Its CLI is marked work in
progress, and some current fixture outputs expose unfinished behavior; those examples
are identified below rather than presented as desirable style.

#### Infix direction

LeanFmt uses a leading operator:

```lean
def total :=
  firstLongValue
  + secondLongValue
```

pretty-lean's current [expression fixture][pretty-comment-test] uses the official
trailing-operator direction:

```lean
def total :=
  firstLongValue +
    secondLongValue
```

This is the same fundamental style difference as the official guide comparison.

#### Fitting declaration bodies

LeanFmt keeps a fitting body on the declaration line when the source does not request an
accepted break:

```lean
def origin : Point := { x := 0, y := 0 }
```

pretty-lean's [command-formatting fixture][pretty-command-test] puts the structure body
after `:=`:

```lean
def origin : Point :=
  { x := 0, y := 0 }
```

LeanFmt treats a declaration-body break as a fit and source-break decision. pretty-lean
inherits the break encoded by the parser formatter for that command.

#### Default line width

For an application whose flat form fits within 120 columns but not 90, LeanFmt's default
width produces a continuation:

```lean
def value :=
  buildValueWithALongButReadableName firstLongArgument secondLongArgument
    thirdLongArgument
```

At pretty-lean's default Lean `Format` width of 120, the same breakable group can remain
flat:

```lean
def value :=
  buildValueWithALongButReadableName firstLongArgument secondLongArgument thirdLongArgument
```

Parser-specific mandatory breaks can still make pretty-lean split shorter code. The
example isolates the consequence of the two width defaults rather than claiming that
width is its only layout input.

#### Proof preservation versus proof formatting

LeanFmt normalizes the theorem header but retains the proof subtree's internal source
spacing:

```lean
theorem and_comm (p q : Prop) (hp : p) (hq : q) : q ∧ p := by
  constructor
  · exact    hq
  ·   exact hp
```

pretty-lean's [tactic fixture][pretty-tactic-test] reconstructs and normalizes the proof
as well:

```lean
theorem and_comm (p q : Prop) (hp : p) (hq : q) : q ∧ p :=
  by
  constructor
  · exact hq
  · exact hp
```

The checked-in indentation around `by` is visibly unfinished. The important design
difference is that pretty-lean attempts to own tactic layout, while LeanFmt makes proof
text an escape hatch.

#### Exact token and comment text versus reconstruction

LeanFmt keeps interpolation adjacency and module-comment contents exact:

```lean
/-! ## Combining functions -/

def greet := s!"Hello, {name}!"
```

Current pretty-lean [comment and interpolation fixtures][pretty-comment-test]
reconstruct those forms as:

```lean
/-!## Combining functions -/

def greet := s! "Hello, {name}!"
```

These are current reconstruction artifacts, not useful style ideas. They illustrate why
LeanFmt should retain its token- and comment-preservation invariants even if it adopts
pretty-lean's extension or editor-integration ideas.

#### Named arguments

pretty-lean's [application formatter][pretty-app-formatter] gives applications
containing named arguments all-or-none grouping. The intended target shape is
record-like:

```lean
runOperationWithValidatedVariables
  (schema := schema)
  (variables := variables)
  (operation := operation)
```

LeanFmt currently applies its ordinary application flow, keeping the longest fitting
prefix before wrapping:

```lean
runOperationWithValidatedVariables (schema := schema) (variables := variables)
  (operation := operation)
```

This is a worthwhile style experiment for LeanFmt. It can be expressed as a balanced or
flow rule for the application; it does not require named-argument logic in the renderer.

#### Extended syntax

pretty-lean does not need a handwritten case for every syntax kind. Its source formatter
processes the file header, obtains the environment containing imported parser
extensions, and calls Lean's formatter for each syntax node. `formatterForKind` first
looks for a registered `@[formatter kind]`. If there is none and the kind names a
`ParserDescr`, Lean interprets that parser description as a formatter. Parser definitions
can also acquire generated formatters through `ParserCompiler` and syntax authors can
provide custom combinator formatters.

For example, an imported package can define a new term parser and describe its spacing
with ordinary parser combinators. Once that module is in the environment, pretty-lean
can often format an occurrence without adding a case to its source-file driver:

```lean
import ImportedSyntax

#check unless condition then fallback
```

This is more generic than LeanFmt's current `ruleFor` table. However, “has a generated
formatter” means only that Lean can reconstruct a `Format` document from the grammar. It
does not guarantee a project-quality multiline layout for the construct.

### Is pretty-lean complete enough for mathlib?

Not yet, based on the available evidence. Its architecture is broad enough to **parse
and attempt to format** much of mathlib, but the project does not demonstrate that it can
safely format the mathlib corpus.

The promising part is syntax coverage:

- it processes imports before formatting commands, so mathlib parser extensions are in
  the environment;
- the formatter registry and `ParserDescr` fallback cover many syntax nodes without a
  source-driver case;
- explicit formatter registrations can cover parser combinators whose layout cannot be
  derived automatically;
- it formats parsed surface syntax and does not require successful elaboration.

The missing evidence is more important for a formatter release:

- there is no formatter-specific mathlib corpus run in the repository;
- the ordinary Lean-fork mathlib CI builds mathlib against compiler changes, but it does
  not format every file, check the diff, and rebuild the formatted result;
- the formatter fixtures cover only a small set of commands, matches, `do`, tactics,
  comments, and range formatting;
- current expected outputs contain token-spacing, comment, and proof-indentation
  artifacts;
- the standalone `ppSource` path processes the header and then parses commands with that
  environment; because it does not process each command before parsing the next, syntax
  declared and first used within one file needs explicit coverage, even though the LSP
  path already has a processed command-snapshot chain;
- check mode detects textual changes but there is no equivalent of LeanFmt's token
  preservation, missing-rule, overflow, convergence, and idempotency validation;
- mathlib must be paired with a compatible revision of the pretty-lean toolchain before
  its imported parser and formatter extensions can even be evaluated fairly.

The right conclusion is therefore: pretty-lean has a more generic **coverage mechanism**,
not demonstrated mathlib-grade **formatting correctness**. A credible claim would require
the same sort of fresh-clone validation LeanFmt uses: format all tracked mathlib files,
verify idempotency and source preservation, build the result, and review the scale and
quality of the diff.

## Architecture and product comparison

### LeanFmt: lossless rules over project syntax

LeanFmt loads a parser environment from each file's imports, converts Lean syntax into a
lossless token tree, performs limited regrouping, and separates horizontal spacing,
syntax-specific break rules, and rendering. Unknown syntax remains reconstructible;
diagnostics identify where only the default rule was available.

This design is more complicated than directly pretty-printing an AST, but the complexity
pays for the properties most useful when formatting existing projects:

- custom syntax can still be parsed in its project environment;
- unsupported layout does not imply lost tokens;
- proofs and comment contents remain stable;
- preservation, overflow, missing-rule, convergence, and idempotency failures are
  observable;
- external-project validation can test the formatter on real code before release.

### pretty-lean: formatter definitions beside parser definitions

The generic machinery used by pretty-lean is part of Lean itself, not an API unique to
the fork. [`Lean.PrettyPrinter.Formatter`][lean-formatter] formatting handlers are
registered by syntax kind with `@[formatter]`, and parser combinators can have
`@[combinator_formatter]` implementations. [`Lean.ParserCompiler`][lean-parser-compiler]
derives handlers from parser definitions. The formatter traverses syntax and builds
`Std.Format` values using grouping, filling, nesting, and alignment. This makes layout an
extension point of the language grammar itself.

That is the most architecturally interesting feature for LeanFmt. Syntax authors know
where their constructs may break, while a generic renderer should only decide which
offered breaks fit. LeanFmt already follows this separation internally. It should first
audit and selectively reuse Lean's imported formatter registrations; a public LeanFmt
extension API may still be useful for applications that need to override project style.

The deployment tradeoff is substantial. pretty-lean is a full Lean fork, so using the
formatter means using its compiler and language server. LeanFmt is an ordinary Lake
dependency and can follow a project's pinned official toolchain. That is a better fit for
incremental adoption and CI.

pretty-lean's LSP integration supports full-document formatting and formats commands
overlapping a requested range while emitting other commands verbatim. This command-level
boundary is safer than formatting an arbitrary syntax fragment because parsing and
layout still have complete command context. LeanFmt can borrow that product shape
without borrowing the compiler-fork distribution model.

## What LeanFmt can learn from Lean's APIs

LeanFmt can use more of Lean's formatter infrastructure, but it should use it as
structural metadata rather than replacing the lossless renderer with `ppCommand`.

### Separate pretty-lean's additions from Lean's infrastructure

Most of the generic syntax machinery is official Lean infrastructure already available
to this project: `Formatter`, `ParserCompiler`, the formatter attributes, category
formatters, the token table, and `Std.Format`. LeanFmt does not need a compiler fork to
call those APIs.

The notable pretty-lean additions are the source-file driver, command-based LSP range
formatting, CLI plumbing, inter-command gap handling, and selected style overrides such
as all-or-none named arguments. The lessons divide cleanly:

- borrow command boundaries for safe editor-range operations;
- test named-argument grouping as a style rule;
- use the imported official formatter registry to understand extended syntax;
- do not copy command reconstruction or cleaned-gap splicing into LeanFmt's lossless
  output path.

### Use parser-owned formatters as a generic coverage signal

The most immediately useful APIs are:

- `Lean.PrettyPrinter.Formatter.formatterAttribute`, which stores handlers keyed by
  `SyntaxNodeKind`;
- `Lean.PrettyPrinter.Formatter.formatterForKind`, which resolves a registered handler
  or interprets a `ParserDescr`;
- `Lean.ParserCompiler`, which derives formatter programs from parser definitions and
  their combinators;
- `Lean.PrettyPrinter.Formatter.categoryFormatter`, which recursively chooses handlers
  for term, tactic, command, and other parser categories.

LeanFmt already processes each file's imports before building its syntax tree. At that
point the environment also contains formatter registrations from those imports. When a
node reaches `defaultRule`, LeanFmt could ask whether Lean has a formatter for that kind
and record the result in diagnostics. This would distinguish three cases:

1. LeanFmt has an intentional syntax rule.
2. LeanFmt lacks a rule, but Lean has grammar-derived layout information.
3. Neither system knows how to lay out the node beyond its raw children.

That inventory can be run over external projects before it changes any output. It would
show how much generic coverage Lean's registry actually contributes for mathlib and
other syntax-heavy packages.

### Reuse lexical separation, not stylistic spacing

Lean's formatter uses the active `Parser.TokenTable` and token parser to decide whether
two adjacent emitted words would merge into a different token. LeanFmt can use the same
mechanism as the fallback for **mandatory** separation, especially for custom tokens
loaded from imports.

This should not replace `SpaceRules`. Style decisions such as spaces around `:=`, tight
projection dots, or preserved structure-brace spelling still belong there. The Lean API
can answer “would these lexemes remain distinct without whitespace?” more reliably than
a growing list of token spellings.

### Experiment with a lossless adapter for `Std.Format`

The official formatter's output contains useful generic structure: text, soft and hard
lines, nesting, grouping, filling, and alignment. A prototype could run the Lean
formatter for a node that lacks a LeanFmt rule and align its emitted token sequence with
the node's original lossless leaves. If every emitted token maps unambiguously to one
original token in order, the prototype can translate only the line and relative-indent
structure into LeanFmt break points. Original lexemes and trivia would still be emitted
by LeanFmt.

The adapter must fail closed. It should decline the result when Lean's formatter:

- changes Unicode or ASCII spelling;
- sanitizes an identifier or macro scope;
- inserts or removes parentheses;
- changes interpolation adjacency;
- cannot map comments and tokens one-to-one;
- emits a layout that cannot be represented by balanced or flow break points.

This is an experiment, not an obvious replacement for `defaultRule`. `Std.Format` was
designed to produce text, not to expose source-token-indexed break plans, so recovering a
lossless mapping may prove too brittle. Even a failed prototype would be useful as a
diagnostic oracle for missing rules.

### Parser descriptions may be useful below the rendered document

`ParserDescr` exposes nodes, sequences, alternatives, repetitions, separated lists,
tokens, category references, and trailing parsers. In principle, LeanFmt could interpret
that description directly into a conservative rule skeleton:

- parser sequences provide child order;
- `sepBy` and `sepBy1` identify peer item boundaries;
- parser whitespace combinators identify legal or required breaks;
- category references identify recursively formatted children;
- node and trailing-node descriptions identify the syntax kind's root shape.

The limitation is availability. A syntax kind defined directly by a `syntax` command
usually has an accessible `ParserDescr`; arbitrary parser functions may be opaque or may
only have the formatter generated when their defining module was compiled. LeanFmt
cannot assume that every imported extension exposes a complete grammar description.
The existing Lean formatter registry is therefore a better first integration point than
a new parallel parser compiler.

### Do not require elaboration for formatting

Elaboration would add semantic facts, and an `InfoTree` can associate source syntax with
terms, tactics, declarations, and resolved names. It is tempting to use that information
to distinguish overloaded notation or expanded macros.

It is a poor core dependency for LeanFmt:

- formatting should work on parseable files that are temporarily incomplete or do not
  typecheck;
- elaboration is much more expensive than parsing and can execute project extensions;
- macros may duplicate, discard, or synthesize syntax, weakening the one-to-one mapping
  back to source tokens;
- semantic meaning is rarely needed to decide whitespace around already parsed syntax;
- proof preservation deliberately avoids owning elaborated tactic structure.

Elaboration could be an optional diagnostic experiment—for example, to classify unknown
nodes in a corpus—but should not determine normal output. Processing imported parser
extensions already supplies the syntax awareness needed for formatting surface code.

### Do not replace the lossless pipeline with `ppCommand`

[`ppCommand`][lean-pretty-printer] sanitizes and parenthesizes syntax before producing a
`Format`. pretty-lean's source driver then reconstructs each command and splices cleaned
source gaps between commands. That is compact and enables range formatting, but it is
also why successful formatting can change token-adjacent forms, comment contents,
notation spelling, and proof layout without reporting an error.

LeanFmt's tree, space rules, renderer, and diagnostics remain necessary. The useful Lean
APIs are the parser environment, token table, formatter registry, parser descriptions,
and perhaps the structure of a generated `Format`—not the reconstructed command text.

### Recommended experiment sequence

1. Use the read-only missing-rule audit, which records whether each node has an explicit
   Lean formatter registration, only a `ParserDescr` fallback, or neither.
2. Run that audit over LeanFmt, CSLib, and mathlib; report coverage by syntax kind and
   frequency.
3. Use Lean's token table only for mandatory-separation fallback and verify the existing
   fixtures remain unchanged.
4. Prototype `Std.Format`-to-break-point translation for missing rules, with exact
   one-to-one token alignment and fail-closed behavior.
5. Compare the prototype against handwritten rules on known nodes before enabling it for
   unknown syntax.
6. Keep elaboration out of the production path unless a later experiment demonstrates a
   specific layout decision that parsing and formatter metadata cannot express.

## Recommendations for LeanFmt

### 1. Publish the intentional style differences

Keep a short compatibility note near the beginning of the design document. It should
name, at minimum:

- leading infix operators instead of the official trailing-operator style;
- a leading declaration type colon on wrapped headers;
- deterministic balanced collections where the guide permits alternatives;
- source-sensitive attribute placement, with a required break before a multiline
  declaration;
- lexeme and proof preservation instead of Unicode and tactic-style normalization;
- preservation of both tight and spaced flat structure braces.

These are not defects. Naming them prevents users from assuming that “Lean formatter”
means “automatic enforcement of the standard-library guide.”

### 2. Keep tail indentation as the unifying continuation model

The official guide says that an infix continuation may or may not add indentation based
on readability. LeanFmt must make that judgement mechanically. Head and tail indentation
turn the subjective advice into a consistent rule while retaining relative indentation
inside structures, matches, applications, and nested infix expressions.

Continue expressing syntax rules as break opportunities and relative indentation
profiles. Avoid adding renderer predicates for individual syntax contexts. New cases
should first be explained as head indentation, a tail floor, balanced breaks, or flow
breaks; a renderer change is justified only when none of those concepts can express the
layout.

### 3. Add style-guide compatibility fixture groups

Build focused fixtures from both style guides for the rules LeanFmt intends to share:
applications, declaration and proof bases, `if`, matches, structures, `where`,
termination suffixes, `deriving`, `do`, and non-orphaned delimiters. Put deliberate
divergences in an adjacent group whose names state the choice, such as `leading-infix`,
`leading-declaration-colon`, and `balanced-constructor`.

This will catch accidental drift without turning a flexible human guide into an
incorrect claim of complete conformance.

### 4. Audit Lean's formatter registry before designing another extension API

Lean already provides imported, syntax-kind-indexed formatter registrations. Measure
their coverage on real projects and prototype a fail-closed adapter before creating a
parallel public registry in LeanFmt.

If an eventual LeanFmt extension API is still useful, it should accept additional
mappings from `SyntaxNodeKind` to ordinary LeanFmt rules, with documented precedence and
no access to renderer state. It can coexist with grammar-derived fallback: handwritten
LeanFmt rules define project style, while Lean's registry supplies conservative
structure for otherwise unknown nodes.

### 5. Add standard-input output before LSP range formatting

Support formatting source from standard input and writing the result to standard output,
with an explicit virtual filename or project root when import resolution needs it. This
unlocks simple editor filters and shell pipelines without coupling LeanFmt to a specific
editor protocol.

After that, full-document LSP formatting is a natural integration layer. If range
formatting is added, use complete command boundaries as pretty-lean does. Arbitrary
fragment formatting would conflict with import-dependent parsing, convergence, source
trivia, and tail indentation context

### 6. Retain conservative proof and comment handling

pretty-lean demonstrates both the appeal and the risk of formatting every syntax node.
Proof formatting could eventually be an opt-in subsystem with its own fixtures and
preservation guarantees, but it should not be required for formatting declarations and
propositions. Exact comment contents should remain invariant.

### 7. Keep 90 columns as the default, with explicit project override

The standard-library guide has no fixed width, the community guide uses 100, and Lean's
pretty-printer defaults to 120. This confirms that line width is project policy, not a
Lean language standard.

LeanFmt's 90-column default is coherent with its current fixtures and local style.
Projects with a different convention can pass an explicit width through the CLI. The
repository-level configuration question remains separate: until there is a project
configuration file, CI should pass the intended width directly.

### 8. Continue treating diagnostics as part of formatting correctness

pretty-lean does not currently match LeanFmt's combined preservation,
actionable-overflow, missing-rule, convergence, and optional idempotency checks. Keep
these checks visible in development and external validation. They are especially
important for a conservative formatter: “the output parses” is weaker than “the
formatter changed only what it promised to change.”

## Conclusion

LeanFmt should not try to become an exact implementation of either Lean style guide.
They contain valuable shared conventions, but permit human choices and include editorial
or semantic policies outside a formatter's scope. LeanFmt is better understood as an
opinionated, lossless Lean style with explicit departures where vertical structure is
clearer.

pretty-lean offers the best model for grammar-owned extension rules and editor
integration, but its compiler-fork deployment and current reconstruction artifacts are
poor fits for LeanFmt's conservative adoption story. Its architecture appears capable of
attempting mathlib syntax, but its tests do not establish mathlib-grade formatting
correctness.

The practical direction is therefore evolutionary: keep the present formatting model,
make its differences explicit, test the shared community conventions, audit and
selectively reuse Lean's parser-formatter metadata, and add editor integration without
sacrificing token, comment, proof, or diagnostic guarantees.

## Sources

- [Lean 4 standard-library style guide][lean-style]
- [Lean community library style guide][community-style]
- [Lean formatter registry and combinators][lean-formatter]
- [Lean parser compiler][lean-parser-compiler]
- [Lean pretty-printer entry points][lean-pretty-printer]
- [pretty-lean README and formatter overview][pretty-lean]
- [pretty-lean formatter registry and document construction][pretty-formatter]
- [pretty-lean source-file formatting and fallback behavior][pretty-source]
- [pretty-lean language-server formatting boundary][pretty-lsp]
- [pretty-lean formatting fixtures][pretty-tests]
- [pretty-lean application formatter][pretty-app-formatter]

[lean-style]: https://github.com/leanprover/lean4/blob/master/doc/std/style.md
[community-style]: https://leanprover-community.github.io/contribute/style.html
[lean-formatter]: https://github.com/leanprover/lean4/blob/master/src/Lean/PrettyPrinter/Formatter.lean
[lean-parser-compiler]: https://github.com/leanprover/lean4/blob/master/src/Lean/ParserCompiler.lean
[lean-pretty-printer]: https://github.com/leanprover/lean4/blob/master/src/Lean/PrettyPrinter.lean
[pretty-lean]: https://github.com/wvhulle/pretty-lean
[pretty-formatter]: https://github.com/wvhulle/pretty-lean/blob/master/src/Lean/PrettyPrinter/Formatter.lean
[pretty-source]: https://github.com/wvhulle/pretty-lean/blob/master/src/Lean/PrettyPrinter/Source.lean
[pretty-lsp]: https://github.com/wvhulle/pretty-lean/blob/master/src/Lean/Server/FileWorker/Formatting.lean
[pretty-tests]: https://github.com/wvhulle/pretty-lean/tree/master/tests/server_interactive
[pretty-command-test]: https://github.com/wvhulle/pretty-lean/blob/master/tests/server_interactive/formatting_commands.lean.out.expected
[pretty-comment-test]: https://github.com/wvhulle/pretty-lean/blob/master/tests/server_interactive/formatting_comments.lean.out.expected
[pretty-tactic-test]: https://github.com/wvhulle/pretty-lean/blob/master/tests/server_interactive/formatting_tactics.lean.out.expected
[pretty-app-formatter]: https://github.com/wvhulle/pretty-lean/blob/master/src/Lean/Parser/Term.lean
