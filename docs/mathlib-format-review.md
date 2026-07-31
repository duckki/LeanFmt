# Mathlib formatting review

This document records the visual review of a complete Mathlib formatting run so
the remaining layout work can be addressed without repeating the corpus review.
It is a point-in-time work list, not part of the normative formatting style.

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

## Open findings

### 1. Infix continuations form diagonal staircases

Severity: high.

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

A flat logical infix chain should have one continuation base. The renderer must
not derive each nested operator's indentation from its immediate left child's
ending column.

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

Severity: high.

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

### 5. Declaration colons detach around intervening comments

Severity: medium.

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

### 6. Custom declaration modifiers detach

Severity: medium.

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

### 7. Structure-value `abbrev` declarations detach `where`

Severity: medium.

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

### 8. Let-fallback bars become orphan lines

Severity: medium.

The fallback separator in `let` pattern syntax can be emitted as a line
containing only `|`.

Representative cases:

- `Mathlib/Tactic/ClickSuggestions.lean:134`
- `Mathlib/Tactic/Coe.lean:23`
- `Mathlib/Tactic/Translate/Core.lean:512`

The fallback bar should remain attached to the scrutinee suffix or fallback
body; it must not become an independent visual segment.

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

## Fix plan

Keep each logical fix in a separate commit with focused regression coverage.
After every commit, run the self-format gate and validate GraphQL Lean and
Quantum Computing Lean before reformatting the affected Mathlib batch.

### Phase 1: low-risk syntax-boundary fixes

1. Fix issue 5 by keeping a declaration `:` with the last binder when the next
   emission is an intervening comment. Reuse the renderer's general comment
   boundary behavior; do not add file- or declaration-name checks.
2. Fix issue 8 by regrouping the `let` fallback separator with its owning
   fallback syntax and giving that syntax an explicit low-risk line-break rule.
3. Fix issue 6 by making command modifiers and the following extensible command
   keyword one header segment. Test both `private irreducible_def` and
   `protected irreducible_def`.
4. Fix issue 7 by mapping `abbrev` structure values to the same declaration
   suffix behavior used by other `... where` declarations. Preserve the
   distinct layout of auxiliary `where` blocks.
5. Revalidate only the files and Mathlib batches containing these examples.
   Confirm that no standalone `:`, `|`, modifier, or structure-value `where`
   remains before running the broader repositories.

These fixes should stay in syntax regrouping or line-break rules. They should
not introduce syntax-name checks in the renderer.

### Phase 2: high-risk layout-base fixes

1. Address issue 4 by making conditional branch ownership explicit in the
   syntax tree or rule data. `else` must use the owning `if` base, and each
   branch body must use one child level. Validate nested `if let`, `match`, and
   record-valued branches together.
2. Address issue 3 by defining one relative-rebasing contract for original
   subtrees. Apply it to proofs, `do` bodies, scoped custom commands, and nested
   structure instances. Avoid separate renderer exceptions for each syntax
   kind.
3. Address issue 2 by changing candidate selection so an enclosing structural
   breakpoint wins before nested breaks that would inherit a far-right inline
   column. Cover dependent binders, application arguments, custom commands,
   notation categories, and type ascriptions with the same mechanism.
4. Address issue 1 after issue 2, since both depend on continuation-base
   semantics. Give a same-precedence infix chain one shared base without
   flattening or changing the preserved syntax tree.
5. For every high-risk step, add focused unit tests, regenerate fixtures,
   self-format with exception and idempotency checks, and validate GraphQL Lean
   and Quantum Computing Lean before resetting and reformatting Mathlib at
   width 100.

Do not change issue 9 or the intentional `<|` spacing as part of these fixes.
