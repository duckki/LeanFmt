# Mathlib formatting review

This document records the visual review of a complete Mathlib formatting run so
the remaining layout work can be addressed without repeating the corpus review.
It is a point-in-time work list, not part of the normative formatting style.

## Current status: 2026-08-05

### Structural `cases` checkpoint after `c9f4e8c`

The structural `cases` change after `c9f4e8c` groups a direct target collection,
the complete header, and the outer alternatives as separate semantic layout
owners. This makes alternative boundaries structural without forcing optional
wrapping inside the header. Target collections reuse the existing discriminant
flow, so multiple targets and named discriminants receive the same continuation
and `:` alignment as `match`. Direct role classification excludes proofs,
`using` clauses, and nested tactics; the line-break rule does not search token
text or descendants. No renderer behavior or rule API changed.

On GraphQL's `FieldGroup/PrefixAppend.lean`, formatter time fell from more than
ten hours to 31.7 seconds. A fresh GraphQL validation passed its clean build,
all three formatter batches, and its post-format build in 228 seconds. The
formatted tree changed 26 files by 183 insertions and 201 deletions. Independent
review found the `cases ... with` headers, named discriminants, alternatives,
and nested bodies logically consistent. Quantum validation passed in 163
seconds and produced no formatting diff. Both projects had zero preservation,
overflow, missing-rule, fallback, and idempotency exceptions.

The complete Mathlib `v4.32.0` audit used commit
`81a5d257c8e410db227a6665ed08f64fea08e997`, the Lake cache, line width 100,
only the `Mathlib` directory, and no `--jobs` override. The cache restored 8,451
artifacts with 188 already present, and the clean pre-format build passed all
8,654 jobs in 5 seconds. All 83 formatter batches were covered. Code
preservation, missing-rule, fallback, and idempotency counts were zero. The
formatted tree changed 7,527 files by 314,094 insertions and 273,931 deletions,
and `git diff --check` passed. The post-format build passed all 8,654 jobs in
4,394 seconds. Most formatter batches took roughly 30 to 55 seconds; isolated
heavy batches took roughly 90 to 100 seconds without an increasing trend,
worker failure, or memory pressure.

Seven actionable-width diagnostics remain. They are checkpoint-known or
reproduce with the committed `c9f4e8c` formatter and are therefore independent
of this `cases` change:

- `AlgebraicGeometry/Gluing.lean:119`, 101 columns;
- `AlgebraicGeometry/StructureSheaf.lean:426`, 104 columns;
- `Analysis/CStarAlgebra/GelfandNaimarkSegal.lean:116`, 101 columns;
- `NumberTheory/Bernoulli.lean:285`, 101 columns;
- `NumberTheory/Bernoulli.lean:388`, 103 columns;
- `NumberTheory/Bernoulli.lean:395`, 102 columns;
- `Tactic/GCongr/Core.lean:819`, 104 columns.

Focused tests cover plain, default-only, default-plus-explicit, named,
proof-bearing, nested, `using`, and multiple-target `cases` forms, including
preservation and idempotency. Independent review found no regression in the
changed named-discriminant, `using`, `with`, explicit-alternative, or
default-alternative layouts. A broad review reproduced only the existing
protected-body and standalone-comment families recorded below. A targeted
review also found that source-preserved `cases` branch bodies can remain at the
alternative's indentation; this predates the header change but remains an open
ownership inconsistency. The next high-risk checkpoint should rebase that one
direct body boundary without opening ordinary leaf proof islands. Keep the seven
width shapes as separate generalized consistency fixes rather than adding
`cases` exceptions.

### Validation through `21b19ae`

The renderer-side comment boundary work is committed through `21b19ae` in
three independent changes: `6882d77` handles comment-forced tree boundaries,
`66621fc` preserves the relative indentation of an inline multiline block
comment, and `21b19ae` rebases inline syntax-comment continuations when their
surrounding original-layout tree moves. These changes keep comments as source
trivia. They add neither comment nodes to the syntax tree nor a new rule API.

Fresh GraphQL and quantum validation passed at `21b19ae`. GraphQL formatted 264
files with automatic worker count, zero exceptions, and a clean post-format
build. Its optional cache command was unavailable; the initial build, three
formatter batches, and final build took 59, 13/10/7, and 24 seconds. Five files
changed by 36 insertions and 18 deletions, only at the intended multiline
parenthesized proof-argument boundary. Quantum formatted 21 files with zero
exceptions and no diff; its cache, initial build, formatter, and final build took
14, 42, 16, and 3 seconds. The combined run, including building leanfmt and fresh
clones, took 281 seconds. The syntax-comment continuation refinement also passed
the complete local gate and focused width-100 Mathlib checks. Five affected
Mathlib modules built successfully in 19 seconds.

A complete Mathlib `v4.32.0` run used commit
`81a5d257c8e410db227a6665ed08f64fea08e997`, selected all 8,264 tracked Lean
files under `Mathlib`, used line width 100 and the automatic worker count, and
restored the Lake cache. All 83 formatter batches were covered. Code
preservation, missing-rule, fallback, and idempotency counts were zero. Four
overflow-only diagnostics remain accepted: the 101-column qualified projection
in `AlgebraicGeometry/Gluing.lean:119`, the 104-column protected proof line in
`AlgebraicGeometry/StructureSheaf.lean:426`, and authored trailing comments in
`Tactic/FBinop.lean:225` and `Tactic/GCongr/Core.lean:820`. The complete
post-format build passed all 8,654 jobs in 3,863 seconds. The formatted tree
changed 7,524 files with 311,282 insertions and 271,209 deletions, and
`git diff --check` passed.

The isolated slow geometry/manifold batch was not a regression. On the same
clean 100-file batch, `21b19ae` took 47.40 seconds and an experimental comment
generalization took 46.39 seconds. Focused comparisons against `6f705af` also
showed equivalent formatter time for the three dominant files. No increasing
batch trend, worker failure, or memory pressure was observed.

### Rejected standalone-comment generalization

An experiment removed `preserveNextStandaloneCommentIndent` and attempted to
derive standalone-comment indentation at every pending renderer boundary from
the preceding token's source column and the pending indentation. The complete
83-batch width-100 Mathlib formatter pass remained preservation- and
idempotency-clean, but comparison with the preceding full output changed 33
files and was not visually consistent. It correctly restored several proof-body
comments, including the examples in `Analysis/Calculus/Deriv/Prod.lean` and
`Analysis/LocallyConvex/WithSeminorms.lean`, but it also over-indented peer
comments in inductive declarations, parameter groups, structures, and command
bodies. A continued declaration-result comment in
`CategoryTheory/Limits/HasLimits.lean` could still move to column zero.
Three independent reviews classified the 33 changed files as 20 wholly correct,
9 wholly incorrect, 2 mixed, and 2 ambiguous.

The experiment also initially suppressed the established relocation of a line
comment beside an unchanged `(` or declaration `:`. Giving
`movePendingCommentAfterToken` priority fixed that regression and received
focused coverage, but did not resolve the mixed 33-file indentation result. The
entire experiment was therefore backed out and was not committed. The branch is
clean at `21b19ae`.

The failed attempt establishes a useful constraint for the next fix: a token's
source column does not reveal whether its containing layout moved. A clean
general solution should translate a standalone comment through the existing
`sourceLayoutBaseColumn` and `outputLayoutBaseColumn` anchors before comparing
it with the pending structural indentation. This can distinguish an unchanged
peer comment from a comment inside a body whose parent moved, without checking
Lean syntax kinds or adding a rule API. Before implementation, focused tests
must cover all four shapes: a trailing proof comment, an inductive peer comment,
a moved function-body comment, and comment relocation beside stationary and
moved `(` and `:` tokens.

### Comment-created tree boundaries after `6f705af`

The working tree now treats line comments and multiline block comments as
source trivia with intrinsic, non-removable breaks. The renderer establishes a
generic tree boundary from that break, rebases the complete comment and its
following token to the surrounding tree indentation, and may move the leading
comment beside the preceding token when that complete line fits. Comments are
not added to the syntax tree, and no syntax-specific line-break rule or new rule
API was introduced. Single-line block comments remain inline when the complete
tree fits; ordinary width pressure may break the enclosing tree or the boundary
between the comment and its following token.

The complete local gate passed, including build, tests, development linter,
fixture regeneration and dry check, self-formatting, code preservation,
actionable overflow, missing-rule, fallback, idempotency, and the final
`git diff --check`. A fresh targeted validation at Mathlib `v4.32.0` passed for
`Mathlib/Algebra/Module/Projective.lean`, and the formatted module rebuilt
successfully. The detached result comment now formats as
`: -- then P is projective.` with the result type indented below the comment.
The build reported only the accepted long proof line at line 156. A full
Mathlib rerun has not yet been performed for this working-tree change.

Fresh combined validation also passed for `graphql-lean` and
`quantum-computing-lean` without a `--jobs` override. GraphQL's optional cache
was unavailable; its uncached initial build took 71 seconds, formatter batches
took 13, 13, and 7 seconds, and its post-format build took 27 seconds. Five
files changed by 36 insertions and 18 deletions, solely to move multiline
parenthesized proof arguments onto their ordinary application continuation;
the proof bodies and token sequence were unchanged. Quantum's cache, initial
build, formatter batch, and post-format build took 15, 47, 18, and 3 seconds,
and its formatted tree had no diff. Both projects reported zero code-change,
overflow, missing-rule, fallback, and idempotency exceptions.

The combined run took 296 seconds, 39 seconds above the prior 257-second
baseline. Formatter work increased only from 30 to 33 seconds for GraphQL and
from 16 to 18 seconds for Quantum. The remaining increase was build, clone, or
local Lake-package setup variance, with no increasing batch trend, worker
failure, or memory pressure.

### Working-tree validation after `61d472a`

Four low-risk consistency fixes were validated in the working tree after
`61d472a`. Core postfix indexing and generated prefix-index syntax now use one
delimiter-shape rule: breaks are available inside the index and after the
closing delimiter, but never before the closing `]`. Core `#[...]` arrays now
retain balanced existing layouts for both singleton and multi-item forms. The
opening-delimiter suffix classifier now implements its stated suffix semantics,
so a prefixed opener such as `#[` does not lose the structural break before an
item beginning with `(`. Authored trailing line comments now remain attached to
their code even when the complete line exceeds the configured width; this
removes width-dependent comment relocation from the renderer and leaves comment
attachment to the parsed/source structure. None of these changes adds a rule
API or syntax decision to the renderer.

The complete local gate passed: build, tests, development linter, fixture
regeneration and dry check, self-formatting, code preservation, actionable
overflow, missing-rule, fallback, idempotency, and `git diff --check`. Fresh
external validation then passed for `graphql-lean` and
`quantum-computing-lean` without a `--jobs` override. In the final fresh run,
GraphQL's initial build took 57 seconds, its formatter batches took 11, 12, and
7 seconds, and its post-format build took 24 seconds. Five files changed only
at the already intended parenthesized multiline proof-argument boundary.
Quantum's cache, initial build, formatting, and post-format build took 16, 42,
16, and 3 seconds respectively and produced no diff. The combined run took 257
seconds.

The full Mathlib run used the exact `v4.32.0` commit
`81a5d257c8e410db227a6665ed08f64fea08e997`, selected the 8,264 tracked Lean
files under `Mathlib`, set the line width to 100, and did not pass `--jobs`.
The Lake cache restored 7,970 artifacts in 11 seconds, and the cached
pre-format build passed all 8,654 jobs in 5 seconds. All 83 formatter batches
were exercised. Code preservation, missing-rule, fallback, and idempotency
counts were zero throughout.

Four batches required acceptance of overflow-only diagnostics. Two are the
previously recorded correctly indented lines in
`Mathlib/AlgebraicGeometry/Gluing.lean:119` and
`Mathlib/AlgebraicGeometry/StructureSheaf.lean:426`. Two are the expected
consequence of preserving authored trailing comments:
`Mathlib/Tactic/FBinop.lean:225` is 101 columns and
`Mathlib/Tactic/GCongr/Core.lean:820` is 104 columns. Both comments remain
attached to the code they qualify and begin at the correct logical
indentation. Formatter batches were generally 31 to 59 seconds, with isolated
87-, 95-, 90-, and 76-second outliers at batches 13, 22, 51, and 63. There was
no increasing trend, worker failure, or memory pressure.

The first complete post-format build passed all 8,654 jobs in 3,351 seconds.
After the array fixes, a complete 83-batch rerun and complete build also passed.
The final reviewed executable then exercised all 83 batches once more from
batch 1 without repeating the already clean pre-format build. Formatter batches
took 3,071 seconds in aggregate, with a 35-second median, 45-second 90th
percentile, and 58-second maximum at the known heavy batch 47. There was no
increasing trend, worker failure, or memory pressure. The complete post-format
build passed in 6 seconds, and the final invocation took 3,090 seconds.

The final formatted tree changed 7,524 files, with 310,983 insertions and
270,934 deletions, and `git diff --check` passed. The indexed `MDiff[...]`
representative keeps its closing bracket attached and gives the following
operand its ordinary continuation. The three semantic `shake: keep` import
comments remain attached to their imports. The multi-item `#[...]` in
`Mathlib/Tactic/CategoryTheory/Elementwise.lean:159` now breaks after the
prefixed opener, indents its first tuple item, and closes at the array base.

Three independent final reviews covered the implementation, targeted delimiter
and comment cases, and a broad Mathlib sample. The targeted review found no
issue. The broad review confirmed the new array and indexed layouts and
reproduced only the existing high-risk protected-body rebasing family recorded
below. The implementation review found a separator-classification mismatch, a
generated three-child delimiter wrapper that could be misclassified as a
prefix-index application, and two test gaps. Those were corrected with the
existing rule APIs before the final external runs. The final implementation
requires a following operand for generated prefix-index dispatch and uses the
same lexeme-based trailing-separator classification as breakpoint
normalization.

### Full validation at `61d472a`

The current revision was validated from a fresh checkout of Mathlib `v4.32.0`
at commit `81a5d257c8e410db227a6665ed08f64fea08e997`. The run used the Lake cache,
selected only the 8,264 tracked `.lean` files under `Mathlib`, set the line width
to 100, and did not pass `--jobs`. Cache restoration took 41 seconds and the
cached pre-format build passed all 8,654 jobs in 4 seconds.

All 83 formatter batches were exercised. Code preservation, missing-rule,
fallback, and idempotency counts were zero throughout. Two batches stopped on
accepted indentation-induced line overflows: a 101-column qualified projection
in `Mathlib/AlgebraicGeometry/Gluing.lean:119` and a 104-column protected proof
line in `Mathlib/AlgebraicGeometry/StructureSheaf.lean:426`. The run resumed
after each diagnostic so the remaining corpus was still covered. Formatter
batches took 3,565 seconds in aggregate, with a 37-second median, 59-second
90th percentile, and 104-second maximum at batch 47. The isolated slow batches
did not form an increasing trend, and there was no worker failure or memory
pressure.

The complete post-format build passed all 8,654 jobs in 3,362 seconds. The
formatted tree changed 7,525 files, with 310,964 insertions and 270,916
deletions; `git diff --check` passed. Eight independent domain reviews found no
code-preservation issue, but confirmed that the corpus is not visually
release-ready. The open general families are:

- protected parenthesized `by` bodies can retain the shell column after the
  shell moves; 27 examples were found across the reviewed domains;
- `calc` rows can still use either the `calc` column or a preceding proof body's
  column instead of one shared row base;
- standalone `<|` and its operand can detach from their governing application;
- branch bodies, inline record fields, and nested attribute children can retain
  an obsolete source or opener column;
- declaration-result comments and continued line comments can consume or lose
  their pending structural indentation;
- semantic trailing comments such as `shake: keep` can detach from the import
  they qualify;
- indexed delimiter groups can separate a closing `]` and then over-indent the
  following argument.

These findings are evidence for the existing syntax-grouping, protected-layout,
and continuation-base work. They should not be addressed with path-specific
rules or new rule APIs.

### Earlier validation and fixes

The complete Mathlib validation baseline used leanfmt commit `3f3bd05` against
Mathlib `v4.32.0`. The final invocation resumed at batch 75 after the preceding
batches had passed. Batches 75 through 83 took 31 to 42 seconds each and passed
code preservation, missing-rule, actionable-overflow, fallback, and
idempotency checks. Combined with the persisted state for batches 1 through 74,
all 83 formatter batches passed. The run used the Lake cache, selected only
tracked `.lean` files under `Mathlib`, and did not pass `--jobs`; the formatter
used its default automatic worker count.

The complete post-format build passed all 8,654 jobs in 3,867 seconds. The
resumed validation took 4,203 seconds overall. There were no formatter
exceptions, missing rules, non-idempotent files, worker failures, or memory
pressure. The build emitted only Mathlib long-line and long-file lints. These
remain accepted when an unbreakable line begins at its logical indentation or
the additional file length comes from otherwise sound formatting.

The formatted tree changed 7,512 files. Four independent reviewers scanned
separate Mathlib domains for wrong or missing line breaks and incorrect
indentation. Eight representative findings were then copied to temporary files
and formatted again with the current executable under Mathlib's Lake
environment. Every representative remained unchanged, so the findings below
describe current formatter behavior rather than output left by an earlier
batch. The corpus is build-clean and diagnostics-clean, but it is not yet
visually release-ready.

Three general fixes from this review are now implemented independently. Commit
`8ca47da` gives multiline source slices a continuation margin relative to their
rendered anchor. Commit `9d6eada` rebases `calc` rows from the rendered `calc`
introducer. Commit `e7ba1a3` prevents fit recovery from moving a structural,
multi-token child below the base selected by its parent; atomic recovery remains
available for genuinely unbreakable tokens. These changes refine existing
planner and renderer contracts without adding a public or rule-facing API.

At `e7ba1a3`, focused width-100 checks of ten representatives passed code
preservation, missing-rule, actionable-overflow, fallback, and idempotency in
13 seconds. Their targeted build passed all 3,163 required jobs in 824 seconds,
with only the accepted Mathlib long-line and long-file lints. The
source-comment, detached-`calc`, and moved structural-lambda representatives now
have the intended shape when the comment is one multiline source slice. The
split line-comment continuation, declaration-comment, and peer continuation
representatives still reproduce their open families.

The same revision passed fresh complete validation of `graphql-lean` and
`quantum-computing-lean` without a `--jobs` override. GraphQL's three formatter
batches took 10, 12, and 7 seconds. Quantum's cache phase took 16 seconds, its
initial build took 41 seconds, formatting took 17 seconds, and its post-format
build took 2 seconds. The combined run took 231 seconds. Both formatted
checkouts were byte-clean, and independent diff reviews found no formatting
regression.

The current revision resolves the boundary before a parenthesized multiline
proof argument in the focused representative. The syntax tree already kept each
`by` shell structural and protected only its proof body; the missing invariant
was in flow rendering. A fitting multiline original-layout child no longer
makes its complete flow segment count as flat, and an existing boundary before
that child is taken. The full-corpus review above shows that this is only the
shell-level part of the invariant: protected proof bodies can still retain the
shell's column after the shell moves. This adds no rule API or syntax-specific
renderer check.

Fresh validation passed without a `--jobs` override. GraphQL's initial build
took 56 seconds, its formatter batches took 11, 11, and 8 seconds, and its
post-format build took 24 seconds. Five files changed to put parenthesized proof
arguments on separate continuation lines; independent review found no logical
formatting error. Quantum's cache, initial build, formatter, and post-format
build took 16, 41, 17, and 2 seconds respectively and produced no diff. The
combined run took 257 seconds. The width-100 Mathlib representative passed
preservation and idempotency in 7 seconds, then its 1,331-job target graph
replayed and built successfully in 5 seconds with only accepted lints.

### Current families

| Family | Representative evidence | Intended owner | Risk | Status |
| --- | --- | --- | --- | --- |
| A multiline syntax comment moved from inline to block layout rebases only its opening line | `Mathlib/Tactic/NormNum/Pow.lean:282` | Original-tree source-slice planning | Medium | Resolved by `8ca47da` |
| A detached `calc` keeps its steps at their old source base | `Mathlib/Data/List/Perm/Basic.lean:219` | Syntax grouping and original-tree planning | High | Resolved by `9d6eada` |
| A moved structural, multi-token child can recover an obsolete source column | `Mathlib/Analysis/SpecialFunctions/Integrability/LogMeromorphic.lean:186` | Renderer structural-floor invariant | Medium | Resolved by `e7ba1a3` |
| Parenthesized multiline proof arguments remain attached to an application prefix | `Mathlib/Analysis/BoxIntegral/Partition/Split.lean:155`; `Mathlib/AlgebraicGeometry/Gluing.lean:644` | Generic flow fit and protected-child rebasing | High | Partially resolved: the shell breaks correctly, but protected bodies still retain the shell column |
| A moved `fun`, tactic quotation, or protected body without a parent boundary does not follow its introducer | `Mathlib/Data/Nat/Bitwise.lean:260`; `Mathlib/RingTheory/WittVector/Basic.lean:85`; `Mathlib/Tactic/Linter/MinImports.lean:104`; `Mathlib/Tactic/MinImports.lean:170` | Syntax grouping and original-tree planning | High | Open |
| A standalone `<\|` does not establish the base of its protected operand | `Mathlib/Topology/Sheaves/CommRingCat.lean:311` | Line-break rules and original-tree planning | High | Open |
| Application siblings or declaration-field bodies inherit a preceding token column | `Mathlib/Geometry/Manifold/MFDeriv/SpecificFunctions.lean:277`; `Mathlib/Algebra/Order/Monoid/Defs.lean:28` | Syntax grouping and line-break rules | High | Open |
| A line comment after a standalone declaration `:` consumes the pending result indentation | `Mathlib/Algebra/Module/Projective.lean:281` | Generic comment-boundary handling | Medium | Open |
| A source-preserved line-comment continuation can detach from its first physical line | `Mathlib/Algebra/ContinuedFractions/Computation/Basic.lean:193` | Syntax grouping and original-tree source slices | Medium | Open |
| `calc` rows can disagree on their shared continuation base | `Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean:362` | Original-tree planning and renderer continuation bases | High | Open |
| A branch body can remain aligned with its branch header | `Mathlib/Algebra/BigOperators/Fin.lean:632` | Syntax grouping and original-tree planning | High | Open |
| A source-preserved `cases` body can remain aligned with its alternative | `Mathlib/Data/ENat/Lattice.lean:139`; `Mathlib/Analysis/Meromorphic/Order.lean:198` | Tactic alternative ownership and protected-body rebasing | High | Open; the structural header checkpoint does not open leaf proof islands |
| Inline record and attribute children can inherit the opener's source column | `Mathlib/Lean/Meta/RefinedDiscrTree/Basic.lean:169`; `Mathlib/Algebra/Group/Submonoid/Membership.lean:553` | Syntax grouping and continuation-base planning | High | Open |
| An indexed delimiter group can detach its closing bracket | `Mathlib/Geometry/Manifold/VectorBundle/Hom.lean:97` | Shape-based line-break dispatch | Medium | Resolved in the working tree after `61d472a` by a general delimiter-shape rule |
| A prefixed array opener can stay attached to a multiline parenthesized item | `Mathlib/Tactic/CategoryTheory/Elementwise.lean:159` | Delimiter classification and collection breaks | Low | Resolved in the working tree after `61d472a` by applying opening-delimiter suffix semantics consistently |
| A semantic trailing comment can detach from its command | `Mathlib/Condensed/EffectiveEpi.lean:11` | Comment attachment and command grouping | Medium | Resolved in the working tree after `61d472a` by preserving authored attachment |

These are governing-layout failures, not requests for syntax-specific rule
exceptions. Mathlib paths are regression inputs only. Long unbreakable lines and
formatter-created too-many-lines warnings are not findings when the surrounding
shape is correct.

### Proposed clean next steps

1. **Continue protected shells only where no parent boundary exists.** The
   parenthesized `by` case needed no regrouping because its shell/body ownership
   was already correct and application flow already exposed the required
   boundary. For tactic quotation and remaining protected bodies, first verify
   whether the shell is structural and whether an ordinary parent boundary is
   available. Regroup only the narrowest body that requires preservation; do not
   add token checks to the renderer or a new rule API. This remains high risk
   because changing an island boundary can also change parent fit probes.
2. **Normalize one peer continuation group in the syntax tree.** Start with the
   application/declaration-field staircase representatives. Peers should expose
   one continuation base to existing rules instead of inheriting the preceding
   token's ending column. Keep this separate from protected-body work so a fit
   regression has one owner.
3. **Carry pending child indentation through line comments.** Treat a line
   comment between a structural boundary and its child as trivia for that
   boundary. Group source-preserved physical continuation lines with their
   owning line comment before original-tree planning. The generic boundary state
   should indent both a detached comment and the first following code line,
   while an author-written `: -- comment` remains one line. This should not
   identify declaration syntax or add a comment-specific line-break rule.
4. **Repeat validation in widening rings.** For each commit, run the full local
   gate and its width-100 Mathlib representatives. Then run fresh GraphQL and
   quantum validation. After all three open invariants are accepted in review,
   repeat the complete 83-batch Mathlib run and post-format build.

Each remaining invariant affects shared layout ownership and should stay in its
own commit with independent regression coverage. The renderer should continue
to execute plans and manage output state without identifying Lean syntax kinds.

## Follow-up validation: 2026-08-01

The formatter was validated again at leanfmt commit `dc968e7` against the same
Mathlib `v4.32.0` commit. The run used the Lake cache, selected only tracked
`.lean` files under `Mathlib`, and used the repository's default formatter job
count. All 83 formatter batches passed preservation, missing-rule, overflow,
fallback, and idempotency checks. The complete post-format build passed, and
7,503 changed files were reviewed. The only reported overflow was an accepted
102-column unbreakable line at `Mathlib/Tactic/Ring/Basic.lean:399`; it starts
at the correct logical indentation.

The same formatter revision also passed complete validation and post-format
builds for `graphql-lean` and `quantum-computing-lean`. The GraphQL run changed
eight files without exposing a logical layout error. The quantum run produced
no formatting diff. No formatter exception or material performance regression
was observed in any of the three projects.

Post-fix verification at leanfmt commit `0722403` remained clean:

- `graphql-lean`: the initial 265-job build took 56 seconds, the three formatter
  batches took 11, 12, and 7 seconds, and the post-format build took 31 seconds.
  The same eight files changed, with no new formatting family or exception. Its
  optional cache command was unavailable and was skipped.
- `quantum-computing-lean`: the Lake cache phase took 16 seconds, the initial
  2,653-job build took 42 seconds, formatting took 17 seconds, and the final
  build took 2 seconds. Formatting produced no diff.
- Targeted Mathlib checks took 8 seconds for
  `Mathlib/FieldTheory/SplittingField/Construction.lean` and 5 seconds for
  `Mathlib/GroupTheory/GroupAction/SubMulAction/OfFixingSubgroup.lean`. Both
  passed preservation, missing-rule, overflow, fallback, and idempotency checks.
  These targeted runs intentionally skipped the already-completed full builds.

### Follow-up rule families

The follow-up review found the families below. A fix should describe a general
syntax or layout invariant and live in the layer that owns that invariant. A
Mathlib path is evidence and regression input, never a condition in formatter
code.

| Family | Intended owner | Risk | Status |
| --- | --- | --- | --- |
| Explicitly named indexed infix notation such as `->e[phi]` can detach its closing `]` | Syntax-tree grouping | Low | Resolved |
| A multiline named argument can leave its closing `)` at the value body's indentation | Line-break rules | Low | Resolved |
| A low-priority `<\|` can leave a `have` right operand at the pipe's base | Line-break rules | Low | Resolved |
| Protected multiline `fun` operands retain stale indentation after their parent moves | Original-tree layout planning | High | Proposed below |
| `calc` steps can inherit a moved expression's source column instead of the `calc` block base | Original-tree layout planning | High | Proposed below |
| Proof-bearing structure-valued `where` clauses can retain a stale leading boundary | Original-tree classification and layout planning | Medium | Proposed below |
| Mathlib `lemma` equation arms in `mutual` blocks can use the wrong command base | Syntax grouping and original-tree ownership | High | Proposed below |
| Other multiline `<\|` operands can preserve a source column after the pipe moves | Original-tree layout planning | High | Proposed below |

The first three are bounded consistency fixes. Indexed notation should be
recognized from its parsed delimiter shape rather than a generated parser name.
A named argument owns the break before its value, while its closing delimiter is
a tight suffix of that value unless a comment forces a new line. A low-priority
pipe owns the first line of ordinary `by`, `do`, and `calc` operands. Layout-sensitive
binding operands such as `let` and `have` share the indented start-alignment rule.

### Deferred layout-base proposals

1. Give each protected original-layout island an explicit formatted anchor and
   source anchor. Rebase every preserved line by the difference between those
   anchors. This should cover stale multiline `fun`, `calc`, and residual pipe
   operands without syntax checks in the renderer.
2. Distinguish proof-bearing structure values from generic proof-layout islands
   in original-tree classification. The structure value should preserve its
   internal proof layout while allowing the declaration rule to format its
   leading `where` boundary at the command base.
3. Group Mathlib's extensible `lemma` equation declarations into the same
   command-and-equation-arm shape used by core declarations before assigning a
   protected layout. Mutual command indentation should then come from that
   structural group, not from source columns.
4. Treat low-priority infix attachment and protected-right-operand rebasing as
   separate contracts. Line-break rules decide that `<|` owns the operand's
   first line; original-tree planning decides how the remaining source-preserved
   lines move with it.

Representative high-risk examples remain:

- `Mathlib/Algebra/Order/Monoid/Defs.lean:29` for multiline `fun`
- `Mathlib/CategoryTheory/Sites/Presheaf.lean:113` for `calc`
- `Mathlib/CategoryTheory/Abelian/Injective/Resolution.lean:327` for
  proof-bearing `where`
- `Mathlib/AlgebraicGeometry/Morphisms/ChevalleyComplexity.lean:624` for mutual
  lemma equations
- `Mathlib/CategoryTheory/Pseudoelements.lean:310` for a protected `<|` operand

Long unbreakable lines and formatter-created too-many-lines warnings remain
accepted when their surrounding formatting shape and logical indentation are
correct.

## Validation baseline

- Review date: 2026-07-30
- leanfmt commit: `935dc60`
- Mathlib tag: `v4.32.0`
- Mathlib commit: `81a5d257c8e410db227a6665ed08f64fea08e997`
- Selected files: tracked `.lean` files under `Mathlib`
- Line width: 100
- Formatter batches: 83 batches covering 8,264 files
- Result: every preservation, missing-rule, overflow, fallback, and idempotency
  check passed
- Post-format build: all 8,654 jobs passed
- Changed files visually reviewed: 7,505

Unbreakable long lines are accepted when they begin at the logical indentation
established by the formatting rules. They are not findings by themselves. The
review below is limited to wrongly inserted line breaks, detached syntax, and
incorrect indentation bases.

## Reviewed findings

### 1. Infix continuations form diagonal staircases

Status: resolved.

Same-precedence operators can inherit the preceding operand's ending column
instead of sharing a structural continuation base.

Representative:
`Mathlib/AlgebraicGeometry/EllipticCurve/Projective/Formula.lean:252`.

```lean
2 * ...
                                                            - 8 * ...
                                                          + 9 * ...
                                                        - 6 * ...
```

The same root problem appears in:

- `Mathlib/Geometry/Euclidean/MongePoint.lean:230`
- `Mathlib/Tactic/GRewrite/Core.lean:432`
- `Mathlib/Tactic/TFAE.lean:74`
- `Mathlib/Tactic/DepRewrite.lean:309`

The representatives had several related causes. Mixed infix operators now
flatten when Lean's trailing parser descriptions report equal binding powers,
and nested pipe projections regroup as one peer chain. `do if-let` action
continuations inherit the conditional base, `leading_parser` arguments use
application flow, and a generated notation break before trailing punctuation
moves after that separator in the renderer.

### 2. Enclosing breakpoints lose priority over nested expression breaks

Status: resolved.

Dependent binders, custom-command arguments, applications, notation parser
categories, and type ascriptions sometimes remain inline until a nested child
breaks from a far-right token column.

Representative cases:

- `Mathlib/CategoryTheory/Abelian/Projective/Resolution.lean:84`: a dependent
  `Σ'` body
- `Mathlib/MeasureTheory/Measure/MeasureSpaceDef.lean:438`:
  `add_aesop_rules` arguments
- `Mathlib/LinearAlgebra/LinearIndependent/Lemmas.lean:757`: nested
  application and type ascription
- `Mathlib/MeasureTheory/Integral/Average.lean:102`: notation parser category

For example, sibling custom-command arguments form a staircase:

```lean
add_aesop_rules safe
                  tactic
                    (rule_sets := [Measurable])
                      (index := [target @AEMeasurable ..])
                        (by fun_prop (disch := measurability))
```

The enclosing comma, operator, or command-argument breakpoint should be
selected before internal child breakpoints when that establishes a normal
structural base.

Generated binder terms are now recognized from their binder shape, recursive
command argument sequences share one continuation base, and notation header
groups expose a flowing outer breakpoint before nested parser-category syntax.

### 3. Moved subtrees retain stale source indentation

Status: resolved.

When formatting moves a parent expression or scoped command, some protected
proofs, custom-command bodies, or nested structure instances retain an old
absolute source indentation.

Representative:
`Mathlib/AlgebraicGeometry/ProjectiveSpectrum/Scheme.lean:294`.

```lean
              ⟨m * i, ⟨proj 𝒜 i a ^ m, by
      rw [← smul_eq_mul]; mem_tac⟩,
```

Other cases:

- `Mathlib/Data/Fin/VecNotation.lean:189`: `dsimproc` moves under
  `open Qq in`, but its `do` body does not move with it
- `Mathlib/RingTheory/HopkinsLevitzki.lean:112`: `by` and its proof body
  receive the same indentation
- `Mathlib/Tactic/Widget/Calc.lean:44`: nested structure instances accumulate
  opener and source columns

Source-preserved subtrees must be rebased relative to the formatted position of
their owning syntax. Structural formatting of a nested structure instance must
also use a parent-relative block base instead of recursively using each visual
opener column.

Protected layouts are now rebased when their parent moves. Singleton `#[…]`
wrappers propagate the enclosing expression base, and tail lifting no longer
replaces a base that a nested structure instance explicitly inherits.

### 4. Branches inherit the wrong owning base

Status: resolved.

An outer `else` can align with an inner `match`, inner `then` body, or other
final child rather than the `if` that owns it.

Representative cases:

- `Mathlib/Util/Notation3.lean:499`
- `Mathlib/Tactic/Explode.lean:154`
- `Mathlib/Tactic/Linter/DeprecatedSyntaxLinter.lean:142`

Related record-valued branches in
`Mathlib/Probability/Kernel/Composition/ParallelComp.lean:47` remain level
with `then` instead of receiving one branch-body indentation level.

Branch keywords should use their owning conditional's base. Branch bodies
should then use one structural level under that base.

Ordinary, dependent, and `if let` conditionals now expose the same owning-base
break structure. Their branch keywords return to that base and branch bodies
receive one child level.

### 5. Declaration colons detach around intervening comments

Status: resolved.

An intrinsic comment break between the declaration type separator and result
type establishes the result continuation. When the complete comment line fits,
the renderer moves the detached comment beside the separator:

```lean
    (h ...)
    : -- then `P` is projective.
      Projective R P := by
```

Representative cases:

- `Mathlib/Algebra/Module/Projective.lean:280`
- `Mathlib/CategoryTheory/Limits/HasLimits.lean:444`
- `Mathlib/Logic/Function/Basic.lean:1252`
- `Mathlib/RepresentationTheory/Rep/Basic.lean:789`

The declaration colon retains its ordinary breakpoint. Comment trivia owns its
physical newline, and the renderer applies the result indentation to the token
after it without requiring a comment-sensitive declaration rule.

### 6. Custom declaration modifiers detach

Status: resolved.

Modifiers are split from the extensible `irreducible_def` command:

```lean
protected
irreducible_def add ...
```

Representative cases:

- `Mathlib/Data/Real/Basic.lean:78`
- `Mathlib/FieldTheory/RatFunc/Basic.lean:79`
- `Mathlib/MeasureTheory/Measure/Stieltjes.lean:523`

Command modifiers should attach to the following command keyword regardless of
whether the command is core syntax or an extension.

Syntax regrouping now separates extension-owned modifier containers from their
command and places both in the annotated-declaration flow.

### 7. Structure-value `abbrev` declarations detach `where`

Status: resolved.

The structure-value suffix is broken as:

```lean
abbrev ... : CompleteAtomicBooleanAlgebra α
  where
```

Representative: `Mathlib/Order/Atoms.lean:561`. The same shape occurs across
Order declarations and in, among others:

- `Mathlib/RepresentationTheory/Continuous/TopRep.lean:236`
- `Mathlib/RingTheory/Localization/Defs.lean:148`
- `Mathlib/SetTheory/ZFC/Basic.lean:79`

This is distinct from an auxiliary definition block. A structure-value
`where` should remain a suffix of the declaration signature, consistently with
other declaration commands.

Flattened declaration values now retain `whereStructInst` as the value child,
so `where` remains attached while the structure fields own their following
breaks.

### 8. Let-fallback bars become orphan lines

Status: resolved.

The fallback separator in `let` pattern syntax can be emitted as a line
containing only `|`.

Representative cases:

- `Mathlib/Tactic/ClickSuggestions.lean:134`
- `Mathlib/Tactic/Coe.lean:23`
- `Mathlib/Tactic/Translate/Core.lean:512`

The fallback bar should remain attached to the scrutinee suffix or fallback
body; it must not become an independent visual segment.

The fallback clause and its continuation are distinct logical nodes. Renderer
comment-boundary handling can force the structural continuation without making
the bar an independent breakable piece.

## Accepted and intentional output

### 9. Adjacent constructor delimiters

Status: accepted for now.

Adjacent `⟨⟨ ... ⟩⟩` delimiters currently accumulate one indentation level per
syntax delimiter even though they form one visual prefix. Representative:
`Mathlib/Algebra/AlgebraicCard.lean:66`.

```lean
⟨⟨
    ...
  ⟩⟩
```

This is known and intentionally deferred. Do not treat it as a validation
failure unless the formatting policy changes.

### Source-break spacing after `<|`

Status: intentional.

`Mathlib/Lean/Expr/Basic.lean:301` formats with two spaces after `<|`:

```lean
<|  if bi.isInstImplicit ...
```

The output reflects the intentional interaction between the preserved source
break boundary and operator spacing. Do not file or fix this as an accidental
duplicate-space issue.

## Completed fix sequence

Each logical fix was kept in a separate commit with focused regression
coverage. The formatter's self-format gate and affected Mathlib representatives
were rerun as the fixes progressed.

### Phase 1: low-risk syntax-boundary fixes (completed)

1. Resolved issue 5 by retaining the declaration's ordinary break before `:`.
   Comments on the following line use the result indentation; comments explicitly
   attached as `: -- comment` remain on the separator line.
2. Fixed issue 8 by regrouping the `let` fallback separator with its owning
   fallback syntax and giving that syntax an explicit low-risk line-break rule.
3. Fixed issue 6 by making command modifiers and the following extensible command
   keyword one header segment, covering both `private irreducible_def` and
   `protected irreducible_def`.
4. Fixed issue 7 by mapping `abbrev` structure values to the same declaration
   suffix behavior used by other `... where` declarations while preserving the
   distinct layout of auxiliary `where` blocks.
5. Revalidated the files and Mathlib batches containing these examples.
   No standalone `:`, `|`, modifier, or structure-value `where` remains.

These fixes stayed in syntax regrouping or line-break rules and did not add
file- or declaration-name checks to the renderer.

### Phase 2: high-risk layout-base fixes (completed)

1. Addressed issue 4 by making conditional branch ownership explicit in the
   syntax tree or rule data. `else` uses the owning `if` base, and each branch
   body uses one child level. Nested `if let`, `match`, and record-valued
   branches are covered together.
2. Addressed issue 3 by defining one relative-rebasing contract for original
   subtrees and applying it to proofs, `do` bodies, scoped custom commands, and
   nested structure instances without separate renderer exceptions for each
   syntax kind.
3. Addressed issue 2 by changing candidate selection so an enclosing structural
   breakpoint wins before nested breaks that would inherit a far-right inline
   column. Dependent binders, application arguments, custom commands, notation
   categories, and type ascriptions use the same mechanism.
4. Addressed issue 1 after issue 2, since both depend on continuation-base
   semantics. Same-precedence infix and pipe-projection chains now share one
   base without changing Lean's parsed syntax or hardcoding operator spellings.
5. Every high-risk step received focused unit coverage, self-format exception
   and idempotency checks, and targeted width-100 Mathlib validation.

Do not change issue 9 or the intentional `<|` spacing as part of these fixes.
