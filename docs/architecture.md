# LeanFmt architecture

This document explains the implementation choices behind LeanFmt. It is written for
contributors who want to understand or reproduce the formatter, not for users deciding
whether they like the style. For style rules and examples, see [design.md](design.md).
For build, test, debugging, and profiling commands, see [development.md](development.md).

LeanFmt is a structure-preserving formatter. It parses Lean source with Lean's own
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
custom syntax, layout-sensitive proof blocks, and empty parser wrapper nodes. LeanFmt
keeps that tree close to the source and introduces only the logical regrouping needed by
rules.

## Module map

The implementation is split by responsibility:

| Module | Responsibility |
| --- | --- |
| `LeanFmt.SyntaxTree` | Parse Lean source, keep token/trivia spans, build raw tree, regroup selected raw syntax into logical nodes. |
| `LeanFmt.Formatter.SpaceRules` | Decide horizontal whitespace and trivia cleanup between adjacent emitted tokens. |
| `LeanFmt.Formatter.LineBreakRules` | Define rule-facing segments, rule context, break points, node-kind dispatch, and syntax-specific break judgements. |
| `LeanFmt.Formatter.Renderer` | Carry render state, run fit checks, collect accepted source breaks, compute indentation, emit tokens. |
| `LeanFmt.Formatter.Trace` | Record and format renderer traces for debugging. |
| `LeanFmt.Formatter.Diagnostics` | Analyze compact bang syntax, code preservation, overflow, and missing formatting rules. |
| `LeanFmt.Formatter` | Public formatting API plus `Debug` and `Internal` namespaces for tracing, profiling, and shared pipeline phases. |
| `LeanFmt.Cli` | Command-line argument parsing, file discovery, check mode, validation checks, and executable entry point. |

The test-only executable is separate:

| Module | Responsibility |
| --- | --- |
| `LeanFmt.Tests.Cli` | Fixture update/check mode, renderer trace printing, and profile output. |
| `LeanFmt.Tests.Main` | Minimal `fmt-test` executable entry point. |
| `LeanFmt.Tests.Suite` | Root of the test library, containing unit-style formatter checks grouped into syntax-tree, basic formatting, expression/renderer, control-flow, collection/declaration, and CLI/architecture suites. |

Every imported test module is rooted at `LeanFmt.Tests`. A downstream package may
therefore define its own top-level `Tests` library without either package claiming the
other package's `Tests.*` modules. Lake package scope does not create a Lean module
namespace, so the namespace is explicit in the module names. The library explicitly uses
`LeanFmt.Tests.Suite` as its root, allowing all imported test sources to live under
`LeanFmt/Tests/` without a `LeanFmt/Tests.lean` forwarding module. Fixtures remain under
`Tests/Fixtures` because the test CLI reads them as files rather than importing them.

## Pipeline

Formatting a file follows this pipeline:

1. Normalize line endings to `\n`.
2. Parse the header and commands with Lean's module parser. The default public API
   uses an environment that imports `Lean` with parser extensions enabled. The CLI
   first reads each file header and, when explicit imports are present, loads an
   import-specific parser environment so project syntax is available while formatting
   that file.
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
  | application
  | infixChain (kind : SyntaxNodeKind)
  | definition
  | annotatedDeclaration
  | signatureParameters
  | matchDiscriminants
  | matchPatterns

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
| `.application` | Lean parser applications are nested per argument, but formatting wants one function-application segment. | Child `0` is the head, children `1...` are arguments in source order. Raw `null` argument containers are spliced. |
| `.infixChain kind` | Same-kind infix peers should break as one balanced chain, and renderer indentation should not infer peer structure from nested raw nodes. | Odd-length array alternating operand, operator, operand. Operands are even indexes; operators are odd indexes. |
| `.definition` | Definitions and abbreviations need one node containing header, assignment marker, body, and suffixes. | The raw `declValSimple` wrapper is spliced so child `4` is the value/body when the recognized shape is present. |
| `.annotatedDeclaration` | Attribute/modifier wrappers must be able to break before the declaration without making plain declarations nontransparent. | Child `0` is the nonempty modifier subtree, child `1` is the declaration, remaining children preserve raw order. |
| `.signatureParameters` | Parameter sequences need flow behavior at binder boundaries without forcing rules to inspect raw `null` wrappers. | Direct binder/parameter children from `optDeclSig` or `declSig`. |
| `.matchDiscriminants` | Multiple match scrutinees need peer flow boundaries after commas, aligned under the first scrutinee, rather than generic nested parser wrapping. | Children of the discriminant sequence immediately before `with`, preserving alternating discriminants and commas. |
| `.matchPatterns` | Multiple patterns in one alternative need peer/balanced wrapping rather than raw nested `null` behavior. | Pattern children from the `matchAlt` pattern wrapper, with a redundant single `null` wrapper removed. |

Regrouping deliberately avoids semantic interpretation. For example, it flattens only
same-kind infix parser nodes; it does not decide operator precedence itself.

### Recognized raw nodes

Most syntax remains `.raw kind`. Rules can still recognize raw kinds when the raw parser
shape is stable enough. Examples include:

- module/header/import commands,
- declarations, structures, inductives, theorems, mutual blocks, and `where` suffixes,
- binders and declaration signatures,
- `let`, `if`, `match`, `do`, lambdas, quantifiers, and subtypes,
- structure instances, arrays, tuples, and parser `null` wrappers under known parents,
- proof escape hatches such as `Lean.Parser.Term.byTactic`.

Binder-name lists are exposed as flow opportunities by rules on their lossless
wrapper segments. Explicit and implicit binders can therefore wrap names before
their type annotation, while untyped quantifier binders can wrap before the
comma. The renderer receives ordinary break points; it does not need to know
which parser wrappers represent binder lists. The enclosing binder rule owns a
separate break before `:`; the name-list flow does not reserve the type as a
same-line suffix.

The full dispatch table lives in `LineBreakRules.ruleFor`. If a raw node is not
recognized, `ruleFor` returns `none`, the renderer uses `defaultRule`, and
`--check-exception` reports the missing rule.

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
  and compact `!value` when source adjacency requires it.
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

structure LineBreakRule where
  name : String
  atomic : Bool := false
  useExistingBreaks : RuleContext -> Segment -> Bool := fun _ _ => false
  mandatory : RuleContext -> Segment -> Bool := fun _ _ => false
  flow : RuleContext -> Segment -> Bool := fun _ _ => false
  inheritBase : RuleContext -> Segment -> Bool := defaultInheritBase
  accumulatesInfixLeftDepth : RuleContext -> Segment -> Bool := fun _ _ => false
  alignStartToIndentation : RuleContext -> Segment -> Bool := fun _ _ => false
  breakPoints : RuleContext -> Segment -> List BreakPoint := fun _ _ => []
```

A `BreakPoint` index means "break before child at this index." `indentLevels` is a
logical two-space continuation count. It is not an absolute column and not a token
anchor.

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
- `mandatory`: returned breaks are structural and are applied without a flat attempt.
- `flow`: returned breaks are candidates; flat layout is tried first, then accepted
  source breaks, then computed wrapping.
- `inheritBase`: this segment uses the surrounding base indentation instead of its
  rendered start column.
- `accumulatesInfixLeftDepth`: broken rendering of prefix pieces contributes to nested
  infix continuation depth. Each broken prefix adds one depth; physical breakpoint
  indentation does not affect this structural count.
- `alignStartToIndentation`: renderer may insert spaces before the first token to move
  a multiline segment to an indentation boundary. Fitting flat segments do not need
  alignment. The `let` rule uses this because Lean's layout parser requires a stable
  indentation column; conditionals use it to keep `if`, `then`, and `else` on a stable
  grid.
- `breakPoints`: logical child boundaries. Rules must not read renderer state.

The default rule is deliberately shape-only. It distinguishes missing children, empty
leaves, nonempty leaves, empty nodes, and nonempty nodes. A nonempty leaf between two
nonempty node children is treated as an infix-like break point; otherwise boundaries
between present children are flow break points. It does not inspect token kind, token
role, or token text.

## Renderer

The renderer owns physical layout. It is the only layer that emits text, measures line
width, tracks current output, and computes indentation.

Core state is:

```lean
structure RenderState where
  source : String
  output : String := ""
  currentLine : String := ""
  lastToken? : Option SyntaxTree.Token := none
  pendingIndent? : Option Nat := none
  segmentBaseColumn : Nat := 0
  segmentIndentation : Nat := 0
  infixLeftDepth : Nat := 0
  infixParentBaseIndentation? : Option Nat := none
  lineFitSuffixWidth : Nat := 0
  context : LineBreakRules.RuleContext := {}
  trace : Trace.State := {}
```

Key fields:

- `currentLine` avoids repeatedly scanning `output` for the current line.
- `lastToken?` lets the renderer ask space rules for inter-token whitespace.
- `pendingIndent?` records a scheduled newline before the next emitted token.
- `segmentBaseColumn` and `segmentIndentation` are the current segment's physical and
  logical bases.
- `infixLeftDepth` accounts for nested broken infix prefixes.
- `infixParentBaseIndentation?` carries a rounded infix parent's break base through
  child rendering. Nested chains combine physical movement from that base with
  structural left depth using their maximum, avoiding both double indentation and
  collapsed inner and outer operators.
- `lineFitSuffixWidth` is trailing same-line width that a recursive child must leave
  room for.
- `context` is the rule ancestor stack.
- `trace` records optional debugging output.

### Rendering algorithm

For each segment:

1. Dispatch to `formattingRuleFor`.
2. Record a trace entry if tracing is enabled.
3. Emit missing and leaf segments mechanically.
4. Emit proof escape-hatch subtrees from original source.
5. If a rule is atomic, render all of its children flat as one measured unit.
6. If a rule is mandatory, apply all returned breaks.
7. If the rule has no break behavior, render children in source order.
8. If `useExistingBreaks` is true, collect source breaks only at returned break points.
   For non-flow rules, any accepted source break applies all rule breaks. For flow rules,
   try the accepted source-break candidate before computed wrapping.
9. Try flat rendering when allowed.
10. For flow rules, try accepted source breaks after flat failure, then computed flow
   wrapping.
11. For non-flow rules with break points, apply all returned breaks simultaneously.

Flat rendering is speculative. The renderer can render into temporary output, check
`maxLineWidth`, and keep or discard that result. This is why rules return only break
opportunities and do not need access to line width.

### Source breaks

The renderer discovers source breaks by looking between adjacent child tokens, but only
breaks accepted by the current rule can be used. Source indentation is ignored. Rules
for declarations, bindings, lambdas, and alternatives do not return break points before
`:=`, `←`, or `=>`; they return an RHS break after the separator instead. The renderer
does not inspect separator spelling. Accepted source breaks and computed rule breaks both
become `pendingIndent?`; later rendering does not distinguish their origin.

For flow rules, accepted source breaks remain selectable opportunities. For non-flow
rules, they are activation signals for the complete balanced rule layout. This is a
renderer invariant, not an opt-in rule predicate.

### Rule consistency invariants

Rules and regroupings should preserve these cross-syntax relationships:

- Non-flow means balanced. A non-flow rule never renders only a source-selected subset
  of its returned break points. Flow rules may select the subset needed to fit.
- A child that is structurally multiline does not fit as a same-line parent operand or
  application argument. The parent breaks before it through ordinary fit/flow logic;
  rules do not accumulate exceptions that prefer a parent break.
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
- Inductive and equation arms inherit the arm base while their binders/patterns use flow
  opportunities. This keeps `|` at the arm base and continuation binders below it.
- A semicolon suppresses the otherwise structural do-statement boundary when the joined
  sequence fits; width pressure can still activate the ordinary sequence layout.
- Interpolated strings are atomic nodes: parents may break before the complete atom, but
  neither `s!` nor interpolation children break independently.
- Comments remain trivia attached to their surrounding tokens. Grouping and balancing
  must preserve comment text and allow the containing rule to recompute indentation.

This separation lets rules say "this boundary may follow source layout" without letting
source indentation leak into renderer state.

### Indentation model

Indentation uses two concepts:

- physical column: where a segment starts on the rendered line,
- logical indentation level: `column / indentationSpaces`.

Breaks are computed by:

```lean
def breakIndent
    (baseColumn baseIndentation infixDepth : Nat) (breakPoint : BreakPoint) : Nat :=
  let addedLevels := infixDepth + breakPoint.indentLevels
  if addedLevels == 0 then
    indentationPastColumn baseColumn
  else
    (baseIndentation + addedLevels) * indentationSpaces
```

Zero-added-level breaks round the physical base column up to an indentation boundary.
This keeps constructs such as match alternatives past a `match` that starts at an odd
column. Breaks with added levels use the floored logical base plus those levels. That is
more conservative for continuations such as application arguments.

Child segment bases are derived from renderer state, not from token spelling. If a child
rule says `inheritBase`, the surrounding segment base is reused. Otherwise the child base
comes from the column where its first visible token will be emitted.

An infix parent also passes its rounded break-base indentation into child state. For a
nested infix chain, effective depth is
`max (currentIndentation - parentIndentation) infixLeftDepth`. Physical movement caused
by parentheses can therefore satisfy structural depth, but an inner operator in the
outer chain's left operand still remains deeper than the outer operator.

### Suffix width

Recursive formatting must account for same-line suffixes owned by parent segments. For
example, when rendering a declaration signature, the parent may later emit ` :=` before
breaking to the body. The signature must leave room for that suffix when deciding
whether its final line fits.

`lineFitSuffixWidth` stores that extra width. The renderer estimates suffix width by
walking following siblings until the next active break boundary and stops at tokens that
are not suffix-eligible. The suffix classifiers live with line-break rules; the renderer
only measures with those classifications.

### Proof and original-source escape hatches

Proof subtrees are not reformatted. When the renderer reaches a recognized proof node, it
emits the original source slice, adjusted only for indentation when needed. Module and
declaration documentation comments are also emitted from their original source slices so
their internal whitespace cannot be changed. This protects tactic scripts, term proof
layout, and comment text while declarations around them can still be formatted.

The escape hatch is intentionally narrow. If a non-proof syntax form is unsafe, prefer a
specific transparent/default rule or a grouping change before adding another original
source region.

## Diagnostics and formatter exceptions

Diagnostics are separate from formatting. The compact-bang diagnostic examines tokens
and reports ambiguous spellings such as `!f a b`, but it does not rewrite them. The
diagnostic API lives under `Formatter.Diagnostics`.

Formatter-exception checking is also separate from rendering. It verifies that the
code-token sequence and exact comment text are preserved, reports remaining line overflow,
and reports missing rules with their source location and tree slice. Preservation
normalization gives every code token and comment boundary one canonical space, so ordinary
formatting whitespace is ignored without conflating tokenizations such as `ab c` and
`a bc`. `ruleFor` returning `none` still renders with `defaultRule`, so unknown nodes remain
conservatively formatable. Diagnostic analysis and the exception model live in
`Formatter.Diagnostics`; trace and profiling APIs live under `Formatter.Debug`;
convergence and shared pipeline phases live under `Formatter.Internal`.

Overflow analysis uses the formatted module's lossless token spans. It ignores comment
overflow, which occupies trivia rather than syntax tokens, and unavoidable overflow where
the entire suffix beyond the width limit is covered by one indivisible unit. Most units are
single tokens. Interpolated strings require explicit tree-span recognition because Lean
parses them as multiple tokens. A comma is also joined to any preceding atomic tree without
requiring a particular array or structure context. An indivisible unit may be followed
immediately by any sequence of tokens in the diagnostic's excluded line-ender set. The set
contains closing delimiters, commas, and semicolons; it is explicit rather than inferred
from parser context. Other overflowing lines still indicate that the formatter left a
possible structural break unresolved.

The CLI reports each exception at its file, continues processing later files, and
aggregates per-kind counts for a final summary. Non-idempotence participates in that CLI
summary even though its extra formatting pass is enabled separately. With diagnostic
checking enabled, `--check` controls writing only; diagnostic exceptions, rather than
ordinary formatting differences, determine failure.

## Why these choices

### Why not Lean's pretty printer?

Lean's pretty printer is semantic and elaboration-oriented. LeanFmt needs to preserve
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
the renderer.

### Why rule and renderer separation?

Rules know syntax. The renderer knows columns. Keeping those concerns separate prevents
renderer code from asking what token or tree kind it is rendering in order to choose an
anchor. Anchors remain render-state facts, while rules expose small predicates such as
`inheritBase` and `accumulatesInfixLeftDepth`.

### Why preserve proofs?

Proof scripts are dense, style-sensitive, and often use tactic syntax that changes across
imports. Formatting theorem statements while preserving proof bodies provides useful
formatting without imposing a tactic layout policy.
