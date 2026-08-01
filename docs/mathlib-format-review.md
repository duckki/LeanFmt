# Mathlib formatting review

This document records the visual review of a complete Mathlib formatting run so
the remaining layout work can be addressed without repeating the corpus review.
It is a point-in-time work list, not part of the normative formatting style.

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
| A low-priority `<|` can detach from the first line of a `have` right operand | Line-break rules | Low | Resolved |
| Protected multiline `fun` operands retain stale indentation after their parent moves | Original-tree layout planning | High | Proposed below |
| `calc` steps can inherit a moved expression's source column instead of the `calc` block base | Original-tree layout planning | High | Proposed below |
| Proof-bearing structure-valued `where` clauses can retain a stale leading boundary | Original-tree classification and layout planning | Medium | Proposed below |
| Mathlib `lemma` equation arms in `mutual` blocks can use the wrong command base | Syntax grouping and original-tree ownership | High | Proposed below |
| Other multiline `<|` operands can preserve a source column after the pipe moves | Original-tree layout planning | High | Proposed below |

The first three are bounded consistency fixes. Indexed notation should be
recognized from its parsed delimiter shape rather than a generated parser name.
A named argument owns the break before its value, while its closing delimiter is
a tight suffix of that value unless a comment forces a new line. A low-priority
pipe owns the first line of its right operand, consistently across `by`, `do`,
`calc`, and `have` starts.

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

The declaration type separator may be emitted on a line by itself when a
comment precedes the result type:

```lean
    (h ...)
    :
    -- then `P` is projective.
    Projective R P := by
```

Representative cases:

- `Mathlib/Algebra/Module/Projective.lean:280`
- `Mathlib/CategoryTheory/Limits/HasLimits.lean:444`
- `Mathlib/Logic/Function/Basic.lean:1252`
- `Mathlib/RepresentationTheory/Rep/Basic.lean:789`

When the following syntax is an intervening comment, `:` should remain
attached to the final binder instead of becoming a separator-only line.

The declaration rule now marks the colon as a leading suffix, and the renderer
keeps that suffix with the preceding line before applying the comment-forced
break.

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

1. Fixed issue 5 by keeping a declaration `:` with the last binder when the next
   emission is an intervening comment, reusing the renderer's general comment
   boundary behavior without file- or declaration-name checks.
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
