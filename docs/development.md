# LeanFmt development

This document is for contributors working on LeanFmt itself. For formatting style and
examples, see [design.md](design.md). For the implementation model, see
[architecture.md](architecture.md).

## Prerequisites

LeanFmt is a Lake package. Use the repository's pinned toolchain:

```sh
cat lean-toolchain
```

The normal commands assume you are in the `leanfmt` repository root.

## Build

Build the library and default executable:

```sh
lake build
```

Build only the formatter library:

```sh
lake build LeanFmt
```

Build the public executable:

```sh
lake build fmt
```

The executable is written to:

```sh
.lake/build/bin/fmt
```

## Run the formatter

Format files in place:

```sh
lake exe fmt path/to/File.lean
```

Check without writing:

```sh
lake exe fmt --check path/to/File.lean
```

Format or check a directory:

```sh
lake exe fmt Some/Directory
lake exe fmt --check --recursive Some/Directory
```

`--recursive` or `-r` makes directory arguments include nested `.lean` files.

## Validation checks

The repository uses the same Lake entry points adopted by mathlib and CSLib:

```sh
lake build --wfail
lake test --wfail
lake lint
```

`--wfail` promotes Lean warnings to errors. `lake lint` runs Batteries'
environment linter. The complete local review gate is `make check`; run
`make shellcheck` when changing shell scripts. CI runs these checks for every
pull request.

The project linter driver runs the enabled Batteries environment linters except
`docBlame`. LeanFmt exposes a small public formatter API, but most declarations
are internal implementation details for syntax analysis, layout, diagnostics,
and the CLI. Other linter findings fail the gate and should be fixed rather than
added to a baseline.

These options are intended for formatter development, not everyday user formatting:

```sh
lake exe fmt --check-exception path/to/File.lean
lake exe fmt --check-idempotent path/to/File.lean
lake exe fmt --check --check-exception --check-idempotent --recursive Some/Directory
```

`--check-exception` runs the formatter's internal diagnostic bundle:

- compare the code-token sequence before and after formatting while preserving
  comment text exactly and requiring the parsed syntax shape, with source positions
  erased, to remain unchanged;
- report actionable formatted lines that still exceed the configured width;
- report syntax nodes that have no registered line-break rule, together with a read-only
  audit of Lean's formatter metadata.

Overflow inside comments is ignored. A line is also exempt when every column beyond the
configured width belongs to one indivisible syntax unit, since the renderer has no legal
place to break that suffix. These units include single tokens, interpolated strings, and
atomic syntax elements followed immediately by tokens in the diagnostic's excluded
line-ender set. The set contains closing delimiters and punctuation such as commas and
semicolons that may finish a formatted line.

The bundle is designed to accept additional formatter-development checks later. Any
reported exception makes the command fail and prevents that file from being rewritten.
The formatter still processes the remaining files, then prints counts for every
exception kind at the end.

`--check-idempotent` remains separate because it performs another complete formatting
pass. Non-idempotence is a hard exception and is included in the final exception counts.

When `--check` is combined with either diagnostic option, it becomes a dry-run switch:
files are not rewritten, but merely needing formatting does not make the command fail.
The command succeeds when there are no diagnostic exceptions. Without a diagnostic
option, `--check` retains its ordinary behavior and fails when a file needs formatting.

### Missing-rule exceptions

Missing rules are reported with their source location and original tree slice:

```text
missing rule: path/to/File.lean:line: Lean.Parser.Some.kind
Lean formatter: registered formatter
<original source slice>
```

A listed node is not automatically formatted incorrectly. It means the generic default
rule is being used. Add an explicit rule when the syntax has layout requirements that the
generic rule cannot know, such as projection tightness or mandatory command boundaries.
The `Lean formatter` line classifies the kind as `registered formatter`, `parser
description`, or `no formatter metadata`. The final exception summary counts all three
groups separately. This classification is evidence for rule development only; it neither
delegates rendering to Lean's pretty printer nor makes a missing LeanFmt rule pass.

## Tests

Run the unit-style test suite:

```sh
lake test
```

To build the test library directly:

```sh
lake build LeanFmt.Tests
```

`LeanFmt.Tests.Suite` is the test library root. Its broad suite runners execute the
unit-style checks with `#eval`.

Run fixture checks without rewriting fixture files:

```sh
lake exe fmt-test --update-fixture --check Tests/Fixtures/*/*.leanfmt
```

Update fixture expected output after an intentional formatting change:

```sh
lake exe fmt-test --update-fixture Tests/Fixtures/*/*.leanfmt
```

The `Makefile` wraps the common maintenance commands:

```sh
make test
make lint
make check
```

`make check` is the normal pre-review gate. It builds and tests with warnings as
errors, runs lints, checks fixtures and formatter invariants, and checks the diff
for whitespace errors.

## Fixture format

Formatter fixtures are `.leanfmt` files with two halves separated by:

```text
-----------------------------------------------------------------------------------------
-- leanfmt: expected output below (DO NOT EDIT)
-----------------------------------------------------------------------------------------
```

The first half is the input source. The second half is expected formatter output.

When adding a rule, prefer a focused fixture that shows the smallest useful example and a
unit-style test when the behavior is easier to assert directly in Lean.

## Renderer tracing

Renderer trace output is available through the test executable when updating fixtures:

```sh
lake exe fmt-test --update-fixture --trace-renderer Tests/Fixtures/04-expressions/let-expression.leanfmt
```

The trace interleaves formatted output lines with segment entries. Each entry includes:

- segment path,
- child range,
- node kind,
- selected rule name,
- current column and indentation,
- segment indentation,
- pending indentation,
- `tailIndentation`.

Use traces to answer questions like "which rule introduced this break?" or "what base
indentation did this child receive?" Keep renderer fixes state-based; avoid adding token
or node-kind special cases in renderer code.

## Profiling

The test executable can print formatter phase timings. Add `--check` when
profiling a source file so the command does not rewrite it:

```sh
lake exe fmt-test --profile --check path/to/File.lean
```

Profile output includes normalize, parse, syntax-tree construction, render, and total
format time.

For larger runs, redirect ordinary formatter output and time the command externally:

```sh
time lake exe fmt --check --recursive Some/Directory >/tmp/leanfmt-check.out 2>&1
```

When optimizing, keep a before/after measurement and validate with the normal checks.
Avoid optimizing by moving syntax decisions into the renderer.

## Adding a formatting rule

A typical rule change follows this path:

1. Add or inspect a fixture that reproduces the layout problem.
2. Use `--check-exception` if the syntax may be falling through to `defaultRule`.
3. Use `--trace-renderer` to find the segment path and current rule.
4. If raw parser shape is awkward, add a lossless raw-node decision in
   `SyntaxTree.regroupRawNode`; keep `regroupTree` as the recursive traversal.
5. Add or refine a rule in `LineBreakRules`.
6. Keep rule output logical: break points, soft-source-break policy, mandatory/flow,
   base inheritance, or infix-depth accumulation.
7. Do not make the renderer inspect syntax to solve a local rule problem.
8. Run tests, fixtures, idempotency, and code-preservation checks on representative
   files.

Small parser-wrapper nodes often should be `transparentRule`. Syntax with tight token
requirements, such as projections, should get an explicit rule or transparent dispatch
rather than relying on default flow breaks.

## Adding a space rule

Space rules are local token-pair decisions. Add one only when the decision is independent
of the wider tree and render state. If the answer depends on syntax context, use a tree
rule instead.

After changing space rules, run fixtures that cover:

- comments,
- projection dots,
- braces and brackets,
- declaration punctuation,
- compact bang syntax.

## Release and downstream use

LeanFmt is redistributable as a Lake package. A downstream package can depend on a local
checkout while developing:

```toml
[[require]]
name = "leanfmt"
path = "../lean-tools/leanfmt"
```

A published repository can be consumed with Lake's Git dependency form:

```toml
[[require]]
name = "leanfmt"
git = "https://example.com/leanfmt.git"
rev = "main"
```

Downstream users can run:

```sh
lake exe fmt path/to/File.lean
```

Before cutting a release or sharing a commit, run:

```sh
lake build
lake build LeanFmt.Tests
lake exe fmt-test --update-fixture --check Tests/Fixtures/*/*.leanfmt
```

For a real-world smoke test, run the formatter in
`--check --check-exception --check-idempotent` mode over a separate Lean repository.

## Review checklist

Before asking for review, summarize:

- which rule or renderer behavior changed,
- whether `--check-exception` passed,
- whether formatting is idempotent on affected files,
- which fixtures or unit tests cover the change,
- any missing-rule exceptions intentionally left unresolved.

Do not commit before review unless the reviewer explicitly asks for a commit.

## External validation

The external validator clones CSLib and mathlib, downloads their Lake build caches,
builds each project, checks every tracked Lean file for preservation, unknown
rules, and idempotence in dry-run mode from that project's `lake env`, formats only
after those diagnostics pass, and then builds each project again:

```sh
scripts/validate-external-projects.sh
```

To validate one or more other Git repositories instead of the defaults, pass each
one as `NAME=GIT_URL_OR_PATH`. The validator always makes a fresh scratch clone,
including when the source is a local repository:

```sh
scripts/validate-external-projects.sh my-project=$HOME/target-repo
```

Pass `--files FILE_SELECTOR` to validate a subset of tracked Lean files. A project
can also override the current selector with `NAME=GIT_URL_OR_PATH::FILE_SELECTOR`.
When the selector names a tracked directory, every tracked `.lean` file under that
directory is included. Other selectors are passed to `git ls-files`, so quote
patterns containing `*` to keep the shell from expanding them first:

```sh
scripts/validate-external-projects.sh \
  --files Mathlib/Combinatorics \
  mathlib=https://github.com/leanprover-community/mathlib4.git
```

Clones are recreated under `.scratch/external-validation`. Set
`LEANFMT_VALIDATION_DIR` to use another directory,
`LEANFMT_VALIDATION_SKIP_CACHE=1` to build without downloading caches,
`LEANFMT_VALIDATION_FILE_PATTERN` to change the default file selector, or
`LEANFMT_VALIDATION_BUILD_BATCH_SIZE` to change the selected-module build batch
size. `LEANFMT_VALIDATION_BATCH_SIZE` is still accepted as a legacy fallback for
the build batch size. Formatter invocations are batched separately through
`LEANFMT_VALIDATION_FORMATTER_BATCH_SIZE`, which defaults to `1` so imported
mathlib environments are released at process exit instead of accumulating across
hundreds of files. The formatter imported-environment cache is disabled during
external validation by default; set
`LEANFMT_VALIDATION_FORMATTER_ENV_CACHE_SIZE=N` to allow each formatter process
to retain up to `N` imported environments. External validation also passes
`--import-env-first` to the formatter by default so mathlib files do not first
attempt a whole-file parse with LeanFmt's default Lean environment; set
`LEANFMT_VALIDATION_IMPORT_ENV_FIRST=0` to restore the ordinary CLI strategy of
trying the default environment before loading source imports.

For the default all-file selector, the pre- and post-format build phases run
`lake build`. When a narrower selector is used, the script converts selected
`.lean` paths to module targets and builds those modules in batches. The script
continues after individual phase failures so it can report all issues, then
exits with a nonzero status if any phase failed. Each phase and the final summary
include elapsed wall-clock time. Build-cache retrieval is an optional
optimization: repositories without a `cache` executable are reported as skipped
rather than failed.
