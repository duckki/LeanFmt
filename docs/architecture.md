# leanfmt architecture

This document explains the implementation choices behind leanfmt. It is written for
contributors who want to understand or reproduce the formatter, not for users deciding
whether they like the style. For style rules and examples, see [design.md](design.md).
For build, test, debugging, and profiling commands, see [development.md](development.md).

leanfmt is a structure-preserving formatter. It parses Lean source with Lean's own
parser, converts the raw syntax into a lossless tree, asks syntax rules where line
breaks may occur, and lets one renderer choose physical whitespace and indentation.

## Design constraints

The implementation follows a few constraints that shape the whole codebase:

- Every source token must remain present exactly once and in source order.
- Formatting rules may inspect syntax tree shape, but they must not inspect renderer
  state such as current column, pending indentation, or output text.
- The renderer may inspect rendering state, but it must not make syntax-specific layout
  decisions from token spelling or node kind.
- Space decisions and line-break decisions are separate.
- Proof subtrees are preserved rather than reformatted.
- Unknown syntax must remain formatable and lossless, even when it receives only generic
  wrapping behavior.

These constraints deliberately rule out a classic pretty-printer pipeline that lowers
Lean syntax into an unrelated document algebra. Lean's parser tree contains source spans,
custom syntax, layout-sensitive proof blocks, and empty parser wrapper nodes. leanfmt
keeps that tree close to the source and introduces only the logical regrouping needed by
rules.

## Module map

The implementation is split by responsibility:

| Module | Responsibility |
| --- | --- |
| `LeanFmt.SyntaxTree` | Parse Lean source, keep token/trivia spans, build raw tree, regroup selected raw syntax into logical nodes. |
| `LeanFmt.Formatter.SpaceRules` | Decide horizontal whitespace and trivia cleanup between adjacent emitted tokens. |
| `LeanFmt.Formatter.LineBreakRules` | Define rule-facing segments, rule context, break points, node-kind dispatch, and syntax-specific break judgements. |
| `LeanFmt.Formatter.OriginalTree` | Classify protected source-layout islands and plan their indentation-preserving source emission. |
| `LeanFmt.Formatter.Renderer` | Carry render state, run fit checks, collect accepted source breaks, compute indentation, emit tokens. |
| `LeanFmt.Formatter.Trace` | Record and format renderer traces for debugging. |
| `LeanFmt.Formatter.Diagnostics` | Analyze compact bang syntax, code preservation, overflow, and missing formatting rules. |
| `LeanFmt.Formatter` | Public formatting API plus `Debug` and `Internal` namespaces for tracing, profiling, and shared pipeline phases. |
| `LeanFmt.Cli` | Command-line argument parsing, hidden-aware file discovery, check mode, and validation checks. |
| `LeanFmt.Main` | Thin executable entry point that supplies runtime hardware concurrency to the toolchain-independent driver. |

The test-only executable is separate:

| Module | Responsibility |
| --- | --- |
| `LeanFmt.Tests.Cli` | Fixture update/check mode, renderer trace printing, and profile output. |
| `LeanFmt.Tests.Main` | Minimal `fmt-test` executable entry point. |
| `LeanFmt.Tests.Run` | Minimal `leanfmtTest` executable entry point for `lake test`. |
| `LeanFmt.Tests.Suite` | Root of the test library, containing unit-style formatter checks grouped into syntax-tree, basic formatting, expression/renderer, control-flow, collection/declaration, and CLI/architecture suites. |

Every imported test module is rooted at `LeanFmt.Tests`. A downstream package may
therefore define its own top-level `Tests` library without either package claiming the
other package's `Tests.*` modules. Lake package scope does not create a Lean module
namespace, so the namespace is explicit in the module names. The library explicitly uses
`LeanFmt.Tests.Suite` as its root, allowing all imported test sources to live under
`LeanFmt/Tests/` without a `LeanFmt/Tests.lean` forwarding module. Fixtures remain under
`Tests/Fixtures` because the test CLI reads them as files rather than importing them.

The Batteries environment linter lives in a separate Lake package under
`tools/linter`. That package depends on leanfmt by a local path and may pin
development-only lint dependencies. The root package and its manifest therefore
describe only the library and executables distributed to downstream users.

## Pipeline

Formatting a file follows this pipeline:

1. Normalize line endings to `\n`.
2. Parse the header and commands with Lean's module parser. The default public API
   uses an environment that imports `Lean` with parser extensions enabled. While each
   command's parser scope is active, probe every layout-delimited `let` body with Lean's
   term parser at application-argument precedence and retain the result as a parser
   fact. The CLI first tries the default environment, then loads an import-specific
   environment when project syntax requires it. For multi-file package formatting,
   files that use the default environment are balanced across worker processes using
   the machine's hardware concurrency. Imported files are grouped by exact normalized
   import header, and every file in one group stays in the same worker. The parent
   obtains the target package's augmented environment from Lake once, then starts all
   formatter workers directly with that process environment.

   An imported worker skips the formatter's default `Lean` environment, reads its
   group's header first, and asks Lean to construct that one exact environment with
   `leakEnv := true`. Every file in the group shares the environment, keyed by the
   ordered imports and import level, and the process exits after the group. This
   matches Lean's one-module process lifetime and avoids reference-count work for an
   environment that survives until process exit. An internal bounded cache can retain
   Lean's opaque `ImportState` after the first direct import when explicitly enabled;
   the normal one-environment worker path uses Lean's direct importer. LeanFmt never
   inspects or reconstructs the state.
   Files with a `module` header use exported `.olean` data; scripts use private data,
   matching Lean's frontend. Lean therefore remains responsible for its import fixed
   point, public/private data selection, IR phases, user initializers, and persistent
   extensions. `LeanEnvironment.lean` is the narrow maintenance boundary for these
   APIs. Driver policy is deliberately separate.

   The automatic imported-environment worker count is capped at two to avoid
   multiplying cold `.olean` I/O and retained environments without bound. The
   scheduler keeps the configured number of one-environment workers active until its
   queue is empty. Worker output is buffered and reported in batch order so diagnostics
   remain readable and deterministic. `-j` or `--jobs` limits concurrent workers.
   Setting `--env-cache-size` to a positive value enables the incremental
   prefix-state path for compatibility testing; zero is the normal direct-import path.

   The parent process keeps the default environment alive while imported workers run,
   so the peak is approximately one default environment plus one custom environment
   per active imported worker. Lean's runtime memory limit is per process and is
   sampled periodically at system-check points; it is not an aggregate budget or a
   concurrency controller. Although Lean exposes current available and constrained
   system memory, neither value predicts the size of the next imported environment.
   LeanFmt therefore uses a conservative imported-worker default and leaves the
   machine-specific choice between one and multiple imported workers to `--jobs`.
3. Convert Lean `Syntax` to a `SyntaxTree.Tree` of tokens and raw parser nodes.
4. Regroup selected raw nodes into logical `SyntaxTree.NodeKind` nodes.
5. Render the resulting tree using line-break rules and space rules.
6. Reparse and rerender until the text reaches a fixed point, subject to the
   hard convergence limit.
7. Clean final trivia and normalize the final newline.

Each convergence pass uses the same parser/tree/rule/renderer pipeline; there is no
separate cleanup layout algorithm. If a construct formats poorly, the fix is to add or
refine a tree grouping, a line-break rule, a space rule, or renderer state logic. The
renderer is the only component that emits text.

`Formatter.Internal.maxConvergencePasses` currently limits formatting to four passes. The
driver tracks previously seen results. A parse failure, cycle, or exhausted pass limit
causes a warning and returns the original normalized source. Fallback is deliberately
nonfatal so `--check-exception` and `--check-idempotent` can report formatter
problems without replacing a file with an unsafe intermediate result. The CLI caches
import-specific environments by the normalized import list to avoid reloading common
project headers for every file.

## Syntax tree

`SyntaxTree.Module` is the parsed source model:

```lean
structure Module where
  source : String
  rawSyntax : Syntax
  tree : Tree
  tokens : Array Token
```

`source` is the normalized source text. `rawSyntax` is Lean's parser output. `tree` is
the regrouped tree used by rules and rendering. `tokens` is a flattened token view used
for reconstruction and diagnostics.

`SourcePositionMap` stores Lean's precomputed line starts for the normalized source.
Renderer and diagnostic column queries share this map instead of rescanning the source
prefix for every token.

Tokens are exact source leaves:

```lean
structure Token where
  role : TokenRole
  kind : SyntaxNodeKind
  value : String
  lexeme : String
  leading : Trivia
  trailing : Trivia
  span : Span
```

`lexeme` is the text the renderer emits. `leading` and `trailing` preserve original
trivia text and spans. Rules must never synthesize replacement token text. Space rules
may clean trivia when using it as inter-token whitespace.

The tree shape is intentionally small:

```lean
inductive NodeKind where
  | raw (kind : SyntaxNodeKind)
  | letExpression
      (kind : SyntaxNodeKind)
      (bodyCanStartApplicationArgument : Bool)
  | application
  | infixChain (kind : SyntaxNodeKind)
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
  | proofBody
  | derivingClause
  | unifConstraints

inductive Tree where
  | missing
  | leaf (token : Token)
  | node (kind : NodeKind) (children : Array Tree)
```

### Raw extraction

`extractRawTree` recursively converts Lean syntax into:

- `.missing` for missing syntax,
- `.leaf` for atoms and identifiers,
- `.node (.raw kind) children` for parser nodes.

Atom and identifier leaves record source spans through `SourceInfo`. Synthetic and none
source-info tokens are preserved as tokens with synthetic trivia and spans.

`Module.reconstruct` sorts all tokens by source span and concatenates each token's full
trivia and lexeme. This is the basic losslessness check: parsing and extracting a tree
must be enough to reconstruct the source.

### Regrouping

Raw parser shape is sometimes inconvenient for formatting. Regrouping is the only phase
that changes tree shape, and it remains token-lossless.

Current logical regroupings are:

| Logical node | Why it exists | Expected children |
| --- | --- | --- |
| `.letExpression kind bodyCanStartApplicationArgument` | Layout-delimited `let` needs a parser-derived answer to whether its body could be consumed as one more right-hand-side application argument. The active parser scope supplies this fact, so imported and locally declared syntax extensions behave according to their precedence without appearing in a formatter keyword list. | The original raw `let`, `letI`, or `letrec` children, unchanged. The raw kind is retained for ordinary rule dispatch and diagnostics. |
| `.application` | Lean parser applications are nested per argument, but formatting wants one function-application segment. | Child `0` is the head, children `1...` are arguments in source order. Raw `null` argument containers are spliced. |
| `.infixChain kind` | Same-kind infix peers should break as one balanced chain, and renderer indentation should not infer peer structure from nested raw nodes. | Odd-length array alternating operand, operator, operand. Operands are even indexes; operators are odd indexes. |
| `.definition` | Definitions, abbreviations, class abbreviations, and extensible declaration commands using Lean's `declValSimple` parser need one node containing header, assignment marker, body, and suffixes. | A raw `declValSimple` wrapper is spliced wherever it occurs among the command's children, leaving `:=` immediately before the value/body. A `whereStructInst` value remains one child so its leading `where` can stay on the final signature line while its fields own the following structural breaks. Only a separate `Term.whereDecls` child is treated as an auxiliary declaration suffix. |
| `.annotatedDeclaration` | Every command form that accepts declaration annotations forms one flow, whether it is built in, introduced by a syntax extension, nested under a command wrapper, recursive under `where`, or a named structure constructor. Source breaks are preserved; otherwise the command remains after its annotations only when the complete command fits on one physical line. The wrapper also establishes the command-line base inherited by modifier and declaration children. | Child `0` contains the leading annotations or, when no annotation is present, the leading declaration modifiers. Any remaining modifiers and the command follow as separate children in source order. An annotation or direct documentation comment embedded in an extensible command node is extracted without changing that command's remaining child indexes; this applies inside scoped-command wrappers as well as at module level. A leading modifier container in an extensible command is removed from that command and placed before it, so the command starts at its keyword and both remain one flow. Optional wrappers around a recursive declaration's attributes are removed. Structure-constructor modifiers are separated from the constructor command so both inherit the structure field base. An inductive constructor keeps its `|` prefix outside the wrapper so annotations that follow it retain source token order. |
| `.signatureParameters` | Parameter sequences need flow behavior at binder boundaries without forcing rules to inspect raw `null` wrappers. | Direct binder/parameter children from declaration signatures, function binders, `termination_by` parameter lambdas, and `unif_hint` commands. In a termination lambda, the final parameter and `=>` share one child so the arrow stays attached while preceding parameters flow at two indentation levels. |
| `.structureHeader`, `.structureConstructor`, and `.structureDeriving` | A structure header may wrap before `extends`, but that continuation must not become the base inherited by constructors, fields, or `deriving`. Separate render scopes let each part own its break and indentation without renderer state exceptions. | The raw structure has a `.structureHeader` first child, ending in `where` when a body is present. It is followed by an optional `.structureConstructor`, the raw `structFields` node directly, and an optional `.structureDeriving`. Structures and classes that only extend parents still receive a header node. The constructor and deriving wrappers contain their original regrouped syntax. |
| `.matchDiscriminants` | Multiple match scrutinees need peer flow boundaries after commas, aligned under the first scrutinee, rather than generic nested parser wrapping. | Children of the discriminant sequence immediately before `with`, preserving alternating discriminants and commas. |
| `.matchPatterns` | Multiple patterns in one alternative need peer/balanced wrapping rather than raw nested `null` behavior. | Pattern children from the `matchAlt` pattern wrapper, with a redundant single `null` wrapper removed. |
| `.doForHeader` | A `for` binder and its collection need separate LHS and `in` layout without teaching the renderer about `do` syntax. | The `for` keyword and declaration children before the loop body. |
| `.doFallbackClause` and `.doFallbackContinuation` | Lean's raw `do` tree may store `| fallback` and later commands in one wrapper. Formatting needs an ordinary optional boundary before the fallback clause and a structural boundary before the later command without a source-dependent breakpoint predicate. The clause delegates ordinary wrapping to its fallback child so `|` stays with the first term; its boundary after `|` activates only when intervening comments need a structural continuation indent. | The clause contains `|` and its fallback body. The continuation contains every following child that belongs to the surrounding `do` sequence. Both `let pattern := value \| fallback` and `let pattern ← action \| fallback` use this shape, including extensible `let_expr` syntax. |
| `.structureUpdate` | The source before `with` behaves as an LHS expression, while the surrounding braces remain an ordinary balanced structure. | The comma-separated source expressions as direct children, including their separators and the final `with` token. Redundant anonymous sequence wrappers are removed. |
| `.ifThenElseClause` and `.ifThenElseChain` | Nested raw `else if` nodes must share one balanced branch decision without making the renderer inspect conditional syntax or ancestor paths. | The chain alternates clause headers and result branches, followed by the final `else` and fallback branch. A clause header contains `if ... then` or `else if ... then` as one transparent segment, so the condition can still wrap by its own rules. Non-chain dependent and `if let` forms use syntax-specific rules with the same owning-base convention: condition continuations and branch bodies indent one level, while `then` and `else` return to the conditional base. |
| `.proofBody` | Tactic syntax after `by` or `decreasing_by` is one protected proof-layout region, including ordinary term proofs, binder default tactics, and termination proofs. | The tactic-sequence children after the separate introducer token. For `binderTactic`, the preceding `:=` also remains a separate sibling. |
| `.derivingClause` | Long deriving-class lists need peer flow boundaries rather than an opaque optional wrapper. | The `deriving` keyword followed by deriving classes and commas as direct children. |
| `.unifConstraints` | Pre-goal `unif_hint` constraints use line breaks as syntax separators and must never be flattened into horizontal whitespace. | The constraint elements between `where` and `⊢` as direct children. |
| Termination suffixes | `termination_by` is an ordinary formatted measure while only the tactic after `decreasing_by` needs proof-layout protection. Both clauses align with the base of their owning declaration. | Optional wrappers under the raw `Termination.suffix` node are removed. A parameter lambda under `terminationBy` exposes its parameter flow before the measure. The outer rule offers only the break after `=>`, so that break is attempted before the nested parameter flow; the nested flow keeps the first parameter after the keyword and indents continuation parameters two levels. `decreasingBy` retains its keyword as one child and wraps only its tactic sequence in `.proofBody`. |
| Lake DSL commands | Lake package and library commands need their `where` configuration body to share the command base, while Git dependency clauses need one rule to own the complete `from git` header and revision suffix. | Optional configuration wrappers are replaced by their `where` and field children. Dependency-name, source, and Git wrappers are spliced into the raw `requireDecl` node in source order. |
| Multi-item delimited collections | Brace terms, arrays, lists, tuples, anonymous constructors, and matrix vectors need one balanced rule to own opening, item, and closing breaks. | Parser sequence wrappers are spliced only when they contain an actual comma or matrix-row semicolon, so delimiters, items, and separators become direct children of the original raw collection node. Unseparated custom-syntax fragments and singleton wrappers remain intact to preserve the established base for one multiline item. |

Regrouping deliberately avoids semantic interpretation. For example, it flattens only
same-kind infix parser nodes; it does not decide operator precedence itself.

The `letExpression` annotation is a syntactic parser fact rather than semantic
interpretation. For each concrete body, `SyntaxTree` runs `termParser argPrec` against
the body's source text in the command's current parser context. A successful prefix parse
means the body could continue the binding's right-hand-side application, so the rule
requires start alignment. A failed probe means the leading syntax itself separates the
body, so visual alignment is only preferred. The probe runs once while parsing the
command; rendering consumes the stored Boolean and never reparses the body. If the
incremental command parser falls back to Lean's full frontend or a source span is
unavailable, the missing fact defaults conservatively to required alignment.

### Recognized raw nodes

Most syntax remains `.raw kind`. Rules can still recognize raw kinds when the raw parser
shape is stable enough. Examples include:

- module/header/import commands,
- declarations, structures, inductives, theorems, mutual blocks, and `where` suffixes,
- binders and declaration signatures,
- `let`, `if`, `match`, `do`, lambdas, quantifiers, and subtypes,
- structure instances, arrays, tuples, and parser `null` wrappers under known parents,
- proof escape hatches such as `Lean.Parser.Term.byTactic` and
  `Lean.Parser.Term.binderTactic`.

Binder-name lists are exposed as flow opportunities by rules on their lossless
wrapper segments. Explicit and implicit binders can therefore wrap names before
their type annotation, while untyped quantifier binders can wrap before the
comma. The renderer receives ordinary break points; it does not need to know
which parser wrappers represent binder lists. The enclosing binder rule owns a
separate break before `:`; the name-list flow does not reserve the type as a
same-line suffix.

The full dispatch table lives in `LineBreakRules.ruleFor`. If a raw node is not
recognized, `ruleFor` returns `none`, the renderer uses `defaultRule`, and
`--check-exception` reports the missing rule. For raw parser kinds, the report also audits
Lean's formatter metadata without using it to change output: it distinguishes an explicit
formatter registration, a generated `ParserDescr` fallback, and a kind with neither.
The missing-rule report intentionally filters unstable implementation-detail kinds such as
tokens, generated private names, custom term-notation names, and `stx` helper nodes.

## Space rules

`SpaceRules` is token-facing. It answers only: what whitespace belongs between two
already-emitted adjacent tokens when the renderer has not scheduled a newline?

Its main entry point is:

```lean
def interTokenWhitespace
    (source : String) (left right : SyntaxTree.Token) (preserveLines : Bool := true) :
    String
```

Important behavior:

- Normalize line endings.
- Remove trailing whitespace before newlines.
- Collapse excessive blank-line runs.
- Preserve and reindent comment trivia.
- Keep tight punctuation such as `(`, `)`, `[`, `]`, commas, semicolons, projection dots,
  fully qualified name-quotation prefixes, and compact `!value` when source adjacency
  requires it.
- Insert a single space between ordinary adjacent code tokens.

Space rules do not inspect `SyntaxTree.Tree`, line width, render state, or ancestors.
When a syntax-aware spacing decision is needed, the syntax should be represented in tree
shape or handled by a line-break rule that changes where tokens are emitted.

## Line-break rules

Line-break rules are syntax-facing. A rule receives a `RuleContext` and a `Segment`.
It returns pure judgements about the current tree segment.

```lean
structure Segment where
  parent : SyntaxTree.Tree
  start : Nat
  stop : Nat

structure RuleContext where
  ancestors : List Frame := []

structure BreakPoint where
  index : Nat
  indentLevels : Nat := 0

inductive StartAlignment where
  | none
  | preferred
  | required

structure LineBreakRule where
  name : String
  atomic : Bool := false
  formatOriginalChildLeadingBoundary
    : RuleContext -> Segment -> Nat -> Bool := fun _ _ _ => false
  keepLeadingSuffixBeforeForcedComment
    : RuleContext -> Segment -> Bool := fun _ _ => false
  keepPrefixWithChildFirstLine
    : RuleContext -> Segment -> Nat -> Bool := fun _ _ _ => false
  useExistingBreaks : RuleContext -> Segment -> Bool := fun _ _ => false
  mandatory : RuleContext -> Segment -> Bool := fun _ _ => false
  flow : RuleContext -> Segment -> Bool := fun _ _ => false
  inheritBase : RuleContext -> Segment -> Bool := defaultInheritBase
  liftsTailIndentation : RuleContext -> Segment -> Bool := fun _ _ => false
  startAlignment : RuleContext -> Segment -> StartAlignment := fun _ _ => .none
  roundUpBaseIndentation : Bool := false
  breakPoints : RuleContext -> Segment -> List BreakPoint := fun _ _ => []
```

A `BreakPoint` index means "break before child at this index." `indentLevels` is a
logical two-space continuation count. It is not an absolute column and not a token
anchor. Every returned point is an ordinary layout opportunity or a structural break
when its rule is mandatory. Break points carry no source-, token-, or comment-dependent
activation predicate.

Top-level command sequences are the one file-layout specialization. `LineBreakRules`
classifies module, header, import, and command sequences and catalogs command nodes as
module keywords, public or ordinary imports, module docstrings, declarations, or other
commands. This exposes syntax facts without encoding vertical spacing in every
`BreakPoint`.

When the renderer processes one of those sequences, it renders each command once and
records whether the result is multiline. Boundaries known from syntax or the previous
command are applied before rendering. If the current command newly requires a blank
boundary, the renderer upgrades only its already-emitted leading whitespace. Import
groups use fixed grouping, module docstrings are separated from following commands, and
adjacent declarations receive a blank line when either renders multiline. Leading
comments and docstrings remain attached to their command. Other syntax sequences retain
the ordinary source-preserving boundary behavior.

`ruleFor : SyntaxTree.Tree -> Option LineBreakRule` is the dispatch table. It has no
ordered candidate list. A known node maps to exactly one rule. Unknown raw nodes return
`none`; `formattingRuleFor` maps that to `defaultRule` for rendering.

The rule module is organized by broad syntax families. Each family keeps its breakpoint
computations and `LineBreakRule` values together; generic wrapper rules and the complete
dispatch table remain at the end.

Rule methods mean:

- `useExistingBreaks`: source breaks at this rule's break points are tried before flat
  layout and can override fitting flat output. For a non-flow rule, one accepted source
  break activates the rule's complete break-point set; partial source layouts are not
  rendered.
- `atomic`: the segment is always rendered flat internally. Its parent still measures
  its complete width and may break before it. Interpolated strings use this so `s!` and
  interpolation contents cannot split independently.
- `formatOriginalChildLeadingBoundary`: the parent rule owns the whitespace before the
  selected original-layout child. The renderer applies ordinary token spacing at that
  boundary and rebases the island's internal source layout to its formatted start
  column. Transparent wrappers use this for later children, so a source newline inside
  a type specification cannot detach its term from the preceding `:`.
- `keepLeadingSuffixBeforeForcedComment`: when a flow child begins with a suffix token
  immediately followed by a comment that forces a line break, keep the fitting suffix
  on the preceding line instead of breaking both before and after it. Declaration
  signatures use this to keep `:` with their final binder without making rules inspect
  comment trivia.
- `keepPrefixWithChildFirstLine`: at a selected child boundary, when the child can format
  its first line beside the already-rendered prefix, delegate wrapping to that child
  rather than taking the boundary immediately before it. Such a rule requires a
  genuinely single-line flat probe and does not reactivate the boundary merely because
  it existed in the source. A comment at that boundary still activates the break, so
  its continuation indentation is structural. Refutable `let` fallback clauses use
  this to keep `|` with the fallback's first term; annotated declarations use it only
  between a modifier container and its extensible command.
- `mandatory`: returned breaks are structural and are applied without a flat attempt.
- `flow`: returned breaks are candidates; flat layout is tried first, then accepted
  source breaks, then computed wrapping. If the accepted source layout still overflows,
  computed wrapping adds breaks without dropping its accepted source boundaries.
  Structure headers use flow so fitting headers stay flat and overflowing headers break
  before `extends`.
- `inheritBase`: this segment uses the surrounding base indentation instead of its
  rendered start column.
- `liftsTailIndentation`: while rendering every child except the final child, establish
  the indentation of the following rule boundary as that child's tail indentation.
  Infix-like and flow rules lift continuations one level beyond that tail. Rules never
  encode prefix widths or variable depth contributions.
- `startAlignment`: rules classify start alignment as absent, preferred for visual
  stability, or required by layout-sensitive parsing. The renderer decides whether
  padding is needed after measuring the nested layout. It may suppress preferred
  alignment immediately after `(`, as for conditionals and syntactically unambiguous
  `let` bodies. Required alignment remains active when Lean's parser reports that a
  layout-delimited body can start an application argument. Explicit
  semicolon-delimited lets use preferred alignment because their body boundary does not
  depend on layout.
- `roundUpBaseIndentation`: positive structural breaks start from the indentation boundary
  after the segment's physical start. Conditionals, delimited structures, tuples, arrays,
  and binding right-hand sides use this so contents remain one full level past an
  off-column head.
- `breakPoints`: logical child boundaries. Rules must not read renderer state, token
  text, comments, or source spacing. Syntax regrouping introduces a logical child when
  the raw parser shape does not expose the boundary a rule needs.

The default rule is deliberately shape-only. It distinguishes missing children, empty
leaves, nonempty leaves, empty nodes, and nonempty nodes. A nonempty leaf between two
nonempty node children is treated as an infix-like break point; otherwise boundaries
between present children are flow break points. It does not inspect token kind, token
role, or token text.

When a known grammar's immediate child shape does not describe its legal layout,
`ruleFor` selects a separate syntax rule instead of weakening this invariant. For
example, a notation whose opening delimiter is part of one composite atom can be
transparent so its enclosed term owns the wrapping, while a bracketed relation can
offer an outer break only before its right operand. These rules classify parser node
kinds; neither the default rule nor the renderer infers the layout from token spelling.

## Renderer

The renderer owns physical layout. It is the only layer that emits text, measures line
width, tracks current output, and computes indentation.

Core state is:

```lean
structure RenderState where
  source : String
  sourceMap : SyntaxTree.SourcePositionMap
  output : String := ""
  currentLine : String := ""
  lastToken? : Option SyntaxTree.Token := none
  pendingIndent? : Option Nat := none
  segmentBaseColumn : Nat := 0
  segmentIndentation : Nat := 0
  sourceLayoutBaseColumn : Nat := 0
  outputLayoutBaseColumn : Nat := 0
  tailIndentation? : Option Nat := none
  tailIndentationStop? : Option Nat := none
  tailIndentationAnchors : List TailIndentationAnchor := []
  breakIndentationShift : Nat := 0
  lineFitSuffixWidth : Nat := 0
  context : LineBreakRules.RuleContext := {}
  trace : Trace.State := {}
```

Key fields:

- `sourceMap` is built once per rendering pass and answers source line/column queries.
- `currentLine` avoids repeatedly scanning `output` for the current line.
- `lastToken?` lets the renderer ask space rules for inter-token whitespace.
- `pendingIndent?` records a scheduled newline before the next emitted token.
- `segmentBaseColumn` and `segmentIndentation` are the current segment's physical and
  logical bases.
- `sourceLayoutBaseColumn` and `outputLayoutBaseColumn` map the nearest enclosing
  source-line layout base to its rendered column. Protected source regions use this
  mapping to move with an enclosing declaration or alternative while retaining their
  internal relative indentation.
- `tailIndentation?` is the indentation floor inherited by continuation lines in the
  current segment. It is a single absolute indentation, not an infix depth counter.
  Child rendering restores the surrounding tail when it returns.
- `tailIndentationStop?` caches the complete segment's final child boundary. Balanced
  slices reuse that boundary instead of treating the slice's final child as the node's
  final child.
- `tailIndentationAnchors` caches each rule boundary's already-computed indentation. A
  non-final child uses the first boundary after it as the base for its contribution,
  falling back to the segment base when no boundary follows it.
- `breakIndentationShift` is the one upward translation shared by every breakpoint in
  the current segment. Computing it once preserves relative indentation and avoids
  recomputing the breakpoint profile during emission.
- `lineFitSuffixWidth` is trailing same-line width that a recursive child must leave
  room for.
- `context` is the rule ancestor stack.
- `trace` records optional debugging output.

`WhitespaceState` is the token-spacing subset of `RenderState`. Both real token
emission and suffix-width measurement use its single `defaultWhitespace` implementation.
The measurement path retains only this smaller state and the measured suffix width, so
it cannot drift into a second whitespace policy.

### Rendering algorithm

For each segment:

1. Dispatch to `formattingRuleFor`.
2. Record a trace entry if tracing is enabled.
3. Emit missing and leaf segments mechanically.
4. Ask `OriginalTree` to plan protected source-island emission and apply the returned
   text and token-state update.
5. If a rule is atomic, render all of its children flat as one measured unit.
6. If a rule is mandatory, apply all returned breaks.
7. If the rule has no break behavior, render children in source order.
8. If `useExistingBreaks` is true, collect source breaks only at returned break points.
   For non-flow rules, any accepted source break applies all rule breaks. For flow rules,
   try the accepted source-break candidate before computed wrapping.
9. Try flat rendering when allowed.
10. For rules that prefer child layouts, try the recursively rendered children when
    the rule-specific prefix remains flat and the complete child layout fits.
11. For flow rules, try accepted source breaks after flat failure, then computed flow
   wrapping that retains those accepted source boundaries while adding any required
   breaks.
12. For non-flow rules with break points, apply all returned breaks simultaneously.

Fit measurement is speculative. The renderer emits into an empty probe while retaining
the current line and pending boundary state, then records two facts from that one result:

- `flat` means the complete segment occupies one physical line.
- `fits` means the result stays within the configured width. It may reuse a multiline
  layout owned by an opaque or already-broken nested child without activating this
  segment's own break points.

Ordinary indented flow may retain the fitting first line of such a nested layout, as in
`f (by` followed by a multiline proof. A zero-indentation flow boundary separates peer
pieces: if the following piece is not flat, the renderer takes the boundary. This is why
a multiline command moves below its annotation without classifying every multiline
application as flat.

This separation keeps line-width and nested-layout decisions in the renderer. Rules
return only break opportunities and do not need access to either fact.

### Source breaks

The renderer discovers source breaks by looking between adjacent child tokens, but only
breaks accepted by the current rule can be used. Source indentation is ignored. Rules
for declarations, bindings, lambdas, and alternatives do not return break points before
`:=`, `←`, or `=>`; they return an RHS break after the separator instead. The renderer
does not inspect separator spelling. Accepted source breaks and computed rule breaks both
become `pendingIndent?`; later rendering does not distinguish their origin.
Blank-line trivia at an accepted break point is a source break too: the renderer
retains one blank line while rebasing the following token to the rule-computed
indentation instead of preserving its old absolute column.

For flow rules, accepted source breaks remain selected if their layout needs additional
computed wrapping; the renderer adds fitting breaks instead of discarding the accepted
ones. For non-flow rules, accepted source breaks are activation signals for the complete
balanced rule layout. This is a renderer invariant, not an opt-in rule predicate.

### Rule consistency invariants

Rules and regroupings should preserve these cross-syntax relationships:

- Non-flow means balanced. A non-flow rule never renders only a source-selected subset
  of its returned break points. Flow rules may select the subset needed to fit.
- A child that is structurally multiline does not fit as a same-line parent operand or
  application argument. The parent breaks before it through ordinary fit/flow logic;
  rules do not accumulate exceptions that prefer a parent break. Annotated declarations
  use the same flow behavior: a multiline command moves below its attribute.
- `:=`, `←`, and `=>` terminate headers. Declaration, binding, lambda, and arm rules
  omit breaks before them and expose RHS breaks after them.
- Header suffixes such as instance `where` and match `with` behave like assignment
  separators: they remain with the header, while their following body owns the break.
- `let ... :=` and `let ... ←` use equivalent header/RHS layout for both identifier
  and destructuring patterns. `def ... :=` and `| ... =>` follow the same separator
  principle with their construct-specific body indentation.
- Peer syntax is regrouped before rules when raw parser nesting would create accidental
  precedence. Same-kind infix operands and multiple match patterns are examples.
- Match discriminants are peer flow items with breaks after commas aligned under the
  first scrutinee. Match arm patterns are non-flow balanced peers: all pattern
  boundaries break together.
- Applications do not special-case `basicFun`, structure instances, `let`, or other
  argument kinds. Their formatted multiline shape is enough to make the application
  break before the argument.
- Fitting constructors are flat. When the enclosing declaration and constructor both
  need breaks, the declaration break after `:=` precedes constructor-internal breaks.
  Anonymous constructors then use balanced item breaks like tuples and arrays.
- Inductive and equation arms inherit the arm base while their binders/patterns use flow
  opportunities. This keeps `|` at the arm base and continuation binders below it.
- A semicolon suppresses the otherwise structural do-statement boundary when the joined
  sequence fits; width pressure can still activate the ordinary sequence layout.
- Interpolated strings are atomic nodes: parents may break before the complete atom, but
  neither `s!` nor interpolation children break independently.
- Comments remain source text between the surrounding lexical tokens. Lean normally
  exposes them as token trivia, but it may leave a comment only in the physical source
  gap after an opening delimiter. Grouping and balancing must preserve that source-gap
  text and allow the containing rule to recompute indentation. A source-broken
  application argument that starts with a delimiter followed by a line comment retains
  its argument break so the delimiter and comment do not migrate onto the preceding
  application line.
- An intrinsically multiline comment at an ordinary rule breakpoint makes that
  renderer boundary structural. This is independent of syntax kind: the renderer
  applies the rule's indentation to both the intervening comment and the following
  token. Line comments force the token after the comment onto a new line, but remain
  attached to preceding code while that complete line fits. Block comments force a
  break only when their own text contains a newline; a one-line block comment may flow
  inline, with its internal text preserved and only surrounding horizontal trivia
  normalized. Syntax-specific rules do not inspect comment text or source spacing.

This separation lets rules say "this boundary may follow source layout" without letting
source indentation leak into renderer state.

### Indentation model

Indentation uses two concepts:

- physical column: where a segment starts on the rendered line,
- logical indentation level: `column / indentationSpaces`.

Breaks are computed by:

```lean
def breakIndent (baseColumn baseIndentation : Nat) (breakPoint : BreakPoint) : Nat :=
  if breakPoint.indentLevels == 0 then
    max (indentationPastColumn baseColumn) (baseIndentation * indentationSpaces)
  else
    (baseIndentation + breakPoint.indentLevels) * indentationSpaces
```

Zero-level breaks round the physical base column up to an indentation boundary while
respecting a larger logical base.
This keeps constructs such as match alternatives past a `match` that starts at an odd
column. Breaks with added levels use the floored logical base plus those levels. That is
more conservative for continuations such as application arguments.

For rules with `roundUpBaseIndentation`, positive breaks first round the physical start
to an indentation boundary. Flow rules retain the conservative logical base instead.

Child segment bases are derived from renderer state, not from token spelling. If a child
rule says `inheritBase`, the surrounding segment base is reused. Otherwise the child base
comes from the column where its first visible token will be emitted.

### Tail indentation

Tail indentation generalizes the indentation needed for a multiline left operand of an
infix operator. A rule establishes a tail for its non-final children through
`liftsTailIndentation`. A child that inherits that tail then adjusts its own balanced,
infix-like, or flow layout. The same mechanism therefore covers applications, binders,
structure updates, and other syntax whose continuation must remain visibly inside a
following boundary.

The model has three terms:

- A segment's **start column** is the physical column of its first visible token.
- Its **head indentation** is
  `indentationLevelForColumn (indentationPastColumn startColumn)`. Rounding is inclusive:
  a start already on the indentation grid stays there; an off-column start moves to the
  next grid column.
- Its **tail indentation** is an absolute logical indentation floor for later lines if
  the segment renders across more than one line. It is not a depth count and is not added
  to a rule's requested indentation.

When a rule sets `liftsTailIndentation`, the renderer caches the complete segment's final
child boundary. Every earlier child inherits the indentation of the following rule
boundary as its tail indentation. Thus a `for` binder is anchored by `in`, an infix
operand by its following operator, and an off-column child by the already-rounded
boundary rather than by the width of its prefix.

For example, an inner operator is lifted beyond the operator that follows its containing
operand:

```lean
- f firstLongArgument
    nextArgument
  - g
:: h
```

Here `::` establishes the outer tail. The left child containing `- g` lifts beyond it,
and the application inside that child retains its own continuation indentation. The
result is a hierarchy of absolute floors, not a sum of operator widths or nesting depths.

At complete-segment entry, the renderer computes the natural indentation of every rule
breakpoint. The least natural indentation is the base of that breakpoint profile. It then
computes the required profile base:

```text
balanced segment:       inherited tail
infix-like/flow segment: max(rounded head, inherited tail + 1)
```

If the required base is higher than the natural base, their difference becomes one
`breakIndentationShift`. The renderer applies that translation to every breakpoint in
the segment. For a zero-level breakpoint, it shifts the final rounded natural
indentation; applying the shift before rounding could make a one-level shift disappear.

Translating the whole profile is essential for balanced syntax. A structure can assign
one natural level to fields and zero to its closing brace:

```lean
-> {
      field1 := value1,
      field2 := value2
    }
    :: rest
```

Shifting those breakpoints together preserves the one-level difference. Clamping each
breakpoint independently to the tail would incorrectly align the fields with the closing
brace.

`tailIndentationStop?` records the final-child boundary of the complete segment, even
while balanced rendering visits slices of that segment. `tailIndentationAnchors` records
the already-computed indentation of each following rule boundary. A non-final child takes
the first anchor after it, merges that floor with an inherited outer tail, and receives
the result in `tailIndentation?`. Nested child rendering is scoped, so this state does not
leak into later siblings.

Transparent parser wrappers inherit the structural base of structure-field default
values. In particular, `binderDefault` does not derive proof indentation from the
physical column after `:=`.

The renderer computes each child's rule and breakpoints once before recursive rendering
and passes that prepared pair into the child call. Layout decisions therefore reuse rule
facts without inferring semantic behavior from the presence or shape of breakpoints.

### Suffix width

Recursive formatting must account for same-line suffixes owned by parent segments. For
example, when rendering a declaration signature, the parent may later emit ` :=` before
breaking to the body. The signature must leave room for that suffix when deciding
whether its final line fits.

`lineFitSuffixWidth` stores that extra width. The renderer estimates suffix width by
walking following siblings until the next active break boundary and stops at tokens that
are not suffix-eligible. The suffix classifiers live with line-break rules; the renderer
only measures with those classifications and the same whitespace policy used by actual
emission. When measurement stops before a token or rule boundary, same-line comment
trivia preceding that boundary still contributes to the fit.

### Proof and original-source escape hatches

Proof subtrees and extensible attribute payloads are not reformatted.
`Formatter.OriginalTree` owns the protected-tree classification, source-slice rebasing,
and emission plan. Classification produces one `LayoutIslandKind`; the renderer retains
that result and passes it into emission instead of repeating the protected-tree scans.
Its renderer-facing API returns the planned text, final token, and the one
comment-boundary flag needed by subsequent ordinary rendering; it does not own or mutate
renderer state. When the renderer reaches a recognized proof or attribute node, it
applies that plan. If the renderer has already formatted the boundary before an island,
that boundary's output column is final; original-tree emission rebases only the island's
source slice and must not apply the source-to-output shift to the boundary again.
A protected subtree that begins on a new source line inherits the source-to-output
layout-base translation established by its enclosing formatted segment. The output-side anchor is
the column where that segment actually starts, including when a child that began a source
line now follows a formatted prefix such as `:`. Every protected line moves by the same
delta. A proof island normally cannot move left of its structural proof indentation,
which keeps a block proof beneath its owning `have` rather than beneath a wrapped type
continuation or outside its declaration. This structural floor is retained even when an
unbreakable tactic line consequently exceeds the configured width. A source-emitted
quotation or compound proof-layout island may instead reduce a uniform shift by whole
indentation levels, never past its original source column. That fit calculation reserves
any closing delimiters and other tight parent suffix that must remain on the island's
last line; excluding that suffix would undercount the actual completed-line width.

If a parent break moves a proof-bearing application, anonymous constructor, structure
instance, or other supported braced proof layout away from its parent-relative source
column, the renderer uses that tree's ordinary structural rule. Equation clauses and
other protected proof-layout shapes remain source islands. The renderer also may retry
an otherwise source-emitted complete delimiter island structurally when doing so removes
an avoidable overflow. Each structural path recomputes the rule's breakpoints because
protected-source emission intentionally does not prepare them. This lets established
collection, field, and nested-expression rules establish a parse-safe block base without
adding syntax decisions to original-source emission.

When a multiline proof or
quotation begins inline, its later source lines use the introducer's source-to-output
movement, clamped to the island's structural indentation, rather than treating the
far-right first token as an indentation anchor. Module and declaration documentation
comments are also emitted from their original source slices so their internal whitespace
cannot be changed. This
protects tactic scripts, term proof layout, quotation bodies, and comment text while
declarations around them can still be formatted. When an original-source child followed
its previous token on the same source line, it honors a pending boundary selected by its
parent rule; an existing source-line boundary and the child's internal layout remain
unchanged.
A proof body whose introducer was moved onto a line by itself starts one indentation
level below that introducer. This structural floor applies only when no code precedes the
introducer on its output line; inline proof islands retain their source-relative layout.
An application whose argument is a proof-bearing `fun` is protected as one layout
island. The syntax tree owns the lambda shell but not the proof body's internal
layout, so moving the application and the proof independently can detach the proof
from the lambda selected by Lean's layout parser.

The escape hatch is intentionally narrow. If a non-proof syntax form is unsafe, prefer a
specific transparent/default rule or a grouping change before adding another original
source region. Mathlib tactic extension nodes whose names start with `Mathlib.Tactic.`
are currently original-source islands because their syntax is extension-owned and often
already encodes tactic-specific layout requirements. Multiline custom braced term
syntax is also emitted from original source so leanfmt does not invent a layout for an
extension-owned DSL whose braces may carry domain-specific structure.
ProofWidgets JSX remains an original-source island, but its complete relative indentation
is rebased when the surrounding formatted layout moves it; leaving a JSX tag at its old
absolute column can change which tokens Lean's layout parser assigns to the element.
When the formatter-selected rebase would newly overflow an atomic JSX line, the renderer
also measures the source layout translated only by its parent layout's movement and uses
that candidate when it has fewer overflows. For `do` bodies, token emission records only
new atomic overflow caused by moving a source token away from a column where it fit.
The outermost eligible `do` sequence considers a source-layout candidate only when that
signal is present. This avoids both repeated nested recovery and reconstructing large
`do` bodies for pre-existing overflow that recovery cannot improve. Rebased original text
is reconstructed token by token so whitespace inside string and other atomic token
lexemes is never changed.
An original-source island whose own source slice is single-line still participates in
ordinary flat-fit checks, so inline extension syntax does not force its parent to break.
The island normally retains its source-leading boundary as well. A surrounding rule can
claim that boundary with `formatOriginalChildLeadingBoundary`; the renderer then supplies
the boundary whitespace and the island preserves only its internal relative layout.
That ownership propagates through leading-child wrapper chains and stops at the first
preceding sibling. A transparent type specification can therefore normalize the boundary
after `:` even when a known application or infix node wraps the extension-owned term,
without claiming spacing inside that known syntax.
Syntax-authoring commands (`syntax`, source-broken `macro` signatures, `macro_rules`,
`elab`, `elab_rules`, and `run_cmd`), Batteries
alias and library-note commands, and other explicitly cataloged extension-owned commands
are layout islands for the same reason. When such a command owns standalone trailing
comments, the original island carries a one-boundary comment-indentation marker so those
comments retain their source indentation without affecting the following formatted
command.

If an unbreakable value already starts on a source line and moving it to the preferred
indentation would create an otherwise avoidable overflow, the renderer first keeps its
source column translated by the parent layout's movement. When a source-broken
application begins with an unbreakable qualified head and that parent-relative column
still overflows, the renderer may use the original absolute source column as a final
fitting candidate. Single tokens, atomic rules, projection-chain heads, multiline atomic
tokens, and quotation islands use the same mechanism. Standalone comment trivia does not
make an otherwise valid structural layout fail its fit probe: the comment follows the
surrounding code's indentation even when the unchanged comment text then exceeds the line
limit. If reformatted code makes an attached line comment overflow, the renderer moves the
unchanged comment text to its own line without changing the following code's indentation.

## Diagnostics and formatter exceptions

Diagnostics are separate from formatting. The compact-bang diagnostic examines tokens
and reports ambiguous spellings such as `!f a b`, but it does not rewrite them. The
diagnostic API lives under `Formatter.Diagnostics`.

Formatter-exception checking is also separate from rendering. It orders source-backed
tokens by their lexeme spans, scans every physical source gap between them for comments,
then compares the code-token sequence and comment text. Line-comment text and relative
block-comment whitespace are exact. A uniform indentation shift of a complete multiline
block comment is normalized against the comment's opening column, allowing the comment
to move with its owning syntax without allowing internal relative whitespace to change.
The check does not rely solely on Lean's token-trivia attachment, because comments after
delimiters may exist only in those source gaps. The check also reports remaining line
overflow and missing rules with their source location and tree slice. Each missing raw
syntax kind is also classified by whether Lean provides a registered formatter, only a
parser-description fallback, or no formatter metadata. This is a read-only coverage audit:
the renderer continues to use leanfmt's `defaultRule`, and non-ignorable missing leanfmt
rules remain exceptions regardless of the Lean formatter classification. Preservation
normalization gives every code token and comment boundary one canonical space, so ordinary
formatting whitespace is ignored without conflating tokenizations such as `ab c` and
`a bc`. `ruleFor` returning `none` still renders with `defaultRule`, so unknown nodes remain
conservatively formatable. Generated private parser node names beginning with `_private.`,
custom term-notation node names such as `termℂ` or `Some.Namespace.termFoo`, token nodes,
and generated `stx` helper names are ignored by missing-rule reporting because they are
not stable rule targets. Diagnostic analysis and the exception model live in
`Formatter.Diagnostics`; trace and profiling APIs live under `Formatter.Debug`;
convergence and shared pipeline phases live under `Formatter.Internal`.

### Preservation-check limitation: layout-sensitive elaboration

The preservation check is necessary but not complete. It compares code-token/comment
fragments and a source-info-stripped syntax signature. Lean elaboration can still change
when formatting changes layout-sensitive source positions that are not represented in
that signature.

Mathlib validation exposed this class of bug:

- repository: `leanprover-community/mathlib4`
- commit: `81a5d257c8e410db227a6665ed08f64fea08e997`
- file: `Mathlib/Combinatorics/SimpleGraph/Triangle/Removal.lean`
- original source lines: `179-186`
- failing formatted build target:
  `Mathlib.Combinatorics.SimpleGraph.Triangle.Removal`

The original source used a layout-sensitive `do` fallback:

```lean
meta def evalTriangleRemovalBound : PositivityExt where eval {u α} _zα pα? e :=
  match pα? with | none => pure .none | some _ => do
  match u, α, e with
  | 0, ~q(ℝ), ~q(triangleRemovalBound $ε) =>
    let .positive hε ← core q(inferInstance) (some q(inferInstance)) ε | failure
    assertInstancesCommute
    pure (.positive q(triangleRemovalBound_pos $hε))
  | _, _, _ => throwError "failed to match on Int.ceil application"
```

An unsafe formatter version produced this patch. The result was parseable and the
token/syntax preservation diagnostics reported no code change, but the post-format build
failed:

```diff
@@
-meta def evalTriangleRemovalBound : PositivityExt where eval {u α} _zα pα? e :=
-  match pα? with | none => pure .none | some _ => do
-  match u, α, e with
-  | 0, ~q(ℝ), ~q(triangleRemovalBound $ε) =>
-    let .positive hε ← core q(inferInstance) (some q(inferInstance)) ε | failure
-    assertInstancesCommute
-    pure (.positive q(triangleRemovalBound_pos $hε))
-  | _, _, _ => throwError "failed to match on Int.ceil application"
+meta
+def evalTriangleRemovalBound : PositivityExt
+  where
+    eval {u α} _zα pα? e :=
+      match pα? with
+      | none => pure .none
+      | some _ => do
+          match u, α, e with
+          | 0, ~q(ℝ), ~q(triangleRemovalBound $ε) =>
+              let .positive hε ←
+                core q(inferInstance) (some q(inferInstance)) ε | failure
+                                                                  assertInstancesCommute
+                                                                  pure
+                                                                    (.positive
+                                                                      q(
+                                                                        triangleRemovalBound_pos
+                                                                          $hε))
+          | _, _, _ => throwError "failed to match on Int.ceil application"
```

The build errors were:

```text
Mathlib/Combinatorics/SimpleGraph/Triangle/Removal.lean:188:14:
Application type mismatch: The argument PUnit.unit has type PUnit.{1}
but is expected to have type Strictness _zα e (some val✝)

Mathlib/Combinatorics/SimpleGraph/Triangle/Removal.lean:195:75:
Unknown identifier `«$hε»`

Mathlib/Combinatorics/SimpleGraph/Triangle/Removal.lean:198:64:
failed to prove positivity/nonnegativity/nonzeroness
```

The architecture response is to give `do` let fallbacks explicit syntax rules.
When a `doIdDecl` or `doPatDecl` contains a fallback tail, the declaration may break
after `←` and before the `|` fallback arm. The wrapper that owns `| fallback` plus the
following `do` continuation forces a break before that continuation. This keeps
continuation commands at the outer `do` indentation instead of allowing them to become
source text after the fallback expression. A fallback containing multiple direct
`do` items receives a structural breakpoint one level beneath the pipe; a single
fallback expression may move onto the pipe line even when the source broke there. The
later continuation still returns to the declaration base. The post-format build remains
the guardrail for preservation classes that syntax diagnostics cannot prove.

A refutable `let pattern := value | fallback` receives the same treatment when
the fallback contains multiple direct `do` statements: the fallback breaks after
`|`, its statements share the one-level-deeper base, and the successful
continuation returns to the declaration base. A single fallback expression may
remain on the pipe line.

Overflow analysis uses the formatted module's lossless token spans. A terminal token
exempts overflow only when the token itself is wider than the configured limit; a token
that fits by itself remains actionable because another rule may move it, unless the
formatted line already consists only of that token and tight excluded line enders at its
structural indentation. Comment-only overflow is similarly exempt when the same literal
comment line occurs in the source, even if formatting moves it to a deeper structural
indentation. New or changed overflowing comment text remains actionable.
Preserved original-source islands and syntax marked atomic by its line-break rule remain
exempt when they cover the entire suffix beyond the width limit. This keeps rendering and
diagnostics consistent for multi-token atomic syntax such as projection suffixes and
interpolated strings. A comma is also joined to any preceding atomic tree without requiring
a particular array or structure context.
An indivisible unit may be followed immediately by any sequence of tokens in the
diagnostic's excluded line-ender set. The set contains closing delimiters, commas, and
semicolons; it is explicit rather than inferred from parser context. Other overflowing
lines still indicate that the formatter left a possible structural break unresolved.
Formatting exception checks compare normalized overflowing line text with the source and
report only newly introduced shapes; unchanged pre-existing overflow remains available
through direct `overflowOccurrences` analysis without being attributed to the formatter.
The standalone analysis keeps layout-island and isolated-token exemptions, while the
source-versus-formatted comparison temporarily removes those movable exemptions. This
reports a movable quotation or isolated token that fit in source but was shifted past
the limit, without reporting the same pre-existing source overflow. Proof and compound
proof-layout islands remain exempt: their proof text is emitted as an indivisible
source-layout unit, so no internal rule boundary is available to resolve an overflow
introduced by a required structural move. For an isolated token, the
comparison maps its token index back to the source and retains the exemption only when
that token's original physical line already overflowed; this covers an unbreakable
declaration name split away from an already-long command prefix.

The CLI reports each exception at its file, continues processing later files, and
aggregates per-kind counts for a final summary. Non-idempotence participates in that CLI
summary even though its extra formatting pass is enabled separately. A file whose first
formatting result equals its source is already a fixed point, so the driver runs the
extra idempotency pass only when formatting changed the text. With diagnostic
checking enabled, `--check` controls writing only; diagnostic exceptions, rather than
ordinary formatting differences, determine failure.

## Why these choices

### Why not Lean's pretty printer?

Lean's pretty printer is semantic and elaboration-oriented. leanfmt needs to preserve
unrecognized syntax, comments, proofs, and exact token text in files that may contain
project-specific parser extensions. A source formatter needs a lossless source tree,
not just pretty-printed elaborated terms.

### Why regroup applications and infix chains?

Parser shape for applications is nested: `f a b` arrives like `((f a) b)`. Formatting
applications wants one head and a list of arguments, so `.application` flattens that
shape.

Infix chains are kept for balanced peer-operator breaks. Raw binary infix trees are
locally usable, but a long chain needs one rule decision over all peer operators. The
`.infixChain` node keeps that syntax reasoning in rules and leaves indentation math in
the renderer. If an infix chain's right operand is an alternating `term | term | ...`
sequence, the infix rule exposes the right-operand boundary and the generic wrapper rule
flows at its bars. This is a shape classification rather than a rule-name or syntax-kind
special case.

### Why rule and renderer separation?

Rules know syntax. The renderer knows columns. Keeping those concerns separate prevents
renderer code from asking what token or tree kind it is rendering in order to choose an
anchor. Anchors remain render-state facts, while rules expose small predicates such as
`inheritBase`, `liftsTailIndentation`, and `roundUpBaseIndentation`.

### Why preserve proofs?

Proof scripts are dense, style-sensitive, and often use tactic syntax that changes across
imports. Formatting theorem statements while preserving proof bodies provides useful
formatting without imposing a tactic layout policy.
