# leanfmt development

This document is for contributors working on leanfmt itself. For formatting style and
examples, see [design.md](design.md). For the implementation model, see
[architecture.md](architecture.md).

## Prerequisites

leanfmt is a Lake package. Use the repository's pinned toolchain:

```sh
cat lean-toolchain
```

The normal commands assume you are in the `leanfmt` repository root.

The root package records our current development toolchain. CI also builds and
tests the same source with supported previous minor versions. Keep compatibility
changes on the main branch rather than maintaining a branch per Lean version.

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
lake exe fmt --line-width 100 --check --recursive Some/Directory
```

`--recursive` or `-r` makes directory arguments include nested `.lean` files.
Hidden entries discovered during directory traversal are skipped unless
`--include-hidden` is passed; an explicitly supplied hidden path is still processed.
`--line-width N` overrides the default 90-character formatter line limit.

## Validation checks

The repository uses the same Lake entry points adopted by mathlib and CSLib:

```sh
lake build --wfail
lake test --wfail
make lint
```

`--wfail` promotes Lean warnings to errors. `make lint` runs Batteries'
environment linter from the separate `tools/linter` Lake package. Batteries is
therefore available to contributors without becoming a dependency of the
released formatter. The complete local review gate is `make check`; run `make
shellcheck` when changing shell scripts. CI runs these checks for every pull
request.

The development linter runs the enabled Batteries environment linters except
`docBlame`. leanfmt exposes a small public formatter API, but most declarations
are internal implementation details for syntax analysis, layout, diagnostics,
and the CLI. Other linter findings fail the gate and should be fixed rather than
added to a baseline.

## Lean-version compatibility

leanfmt supports one source and release line across our current toolchain and
supported previous minor versions. The current-toolchain CI job runs the complete
maintenance gate. Compatibility jobs select each previous minor version in a
disposable checkout and run only the build and test suite. Linting, fixtures,
self-formatting, formatter diagnostics, and idempotency checks run once with our
current toolchain.

When adding or updating leanfmt in a project on an older supported Lean version,
preserve the project's toolchain during dependency resolution:

```sh
lake update --keep-toolchain
```

A normal `lake update` considers direct dependencies' `lean-toolchain` files and
may update the root project to leanfmt's current version. With
`--keep-toolchain`, Lake retains the downstream version and compiles leanfmt with
it. This is required for reliable loading of the project's compiled parser
extensions and imported environment.

Add a maintenance branch for an older Lean version only if its implementation
must diverge from `main`. Ordinary compatibility fixes belong on `main` and must
continue to pass the full toolchain matrix.

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
reported exception makes the command fail. Without `--check`, the formatter still
writes an available checked candidate so a subsequent build can validate that exact
output. A format fallback has no candidate and keeps the source unchanged. The
formatter also processes the remaining files, then prints counts for every exception
kind at the end.

`--check-idempotent` remains separate because changed output requires another complete
formatting pass. Output that already equals its source is a fixed point and does not need
to be recomputed. Non-idempotence is a hard exception and is included in the final
exception counts.

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
delegates rendering to Lean's pretty printer nor makes a missing leanfmt rule pass.

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

leanfmt is redistributable as a Lake package. A downstream package can depend on a local
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
git = "https://github.com/duckki/leanfmt.git"
rev = "v0.2.5"
```

Resolve it without replacing the downstream project's Lean version:

```sh
lake update --keep-toolchain
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

The external validator clones one or more explicitly provided Git repositories,
downloads their Lake build caches, builds each complete project, then formats every
tracked Lean file from that project's `lake env` while checking preservation, unknown
rules, and idempotence. It builds the complete project again after every batch has
been formatted, or after the first failing batch:

```sh
scripts/validate-external-projects.sh $HOME/lean-libs/mathlib4
```

At least one Git repository argument is required; there are no preset targets.
Pass either `GIT_REPO` or `NAME=GIT_REPO`. The source can be a local path or any
clone source accepted by `git clone`. The validator makes a fresh scratch clone
unless `--reuse-clone` is passed:

```sh
scripts/validate-external-projects.sh $HOME/target-repo
scripts/validate-external-projects.sh my-project=$HOME/target-repo
```

Pass `--files FILE_SELECTOR` to validate a subset of tracked Lean files. A project
can also override the current selector with `GIT_REPO::FILE_SELECTOR` or
`NAME=GIT_REPO::FILE_SELECTOR`.
When the selector names a tracked directory, every tracked `.lean` file under that
directory is included. Other selectors are passed to `git ls-files`, so quote
patterns containing `*` to keep the shell from expanding them first:

```sh
scripts/validate-external-projects.sh \
  --files Mathlib/Combinatorics \
  mathlib=https://github.com/leanprover-community/mathlib4.git
```

Validation runs in batches of 100 files by default. The validator first runs one
complete project build. Each validation batch then formats its files directly with
the exception and idempotency checks enabled. Batches continue until all are formatted
or one reports a diagnostic failure. The validator then runs one complete project
build over every candidate written through that point, even when the final formatter
batch failed, so it can also report elaboration or linting failures. Within each batch,
leanfmt manages formatter worker processes and batch sizing. The validator prints the
total file count, total batch count, selected batch, batch index range, first/last file
for each batch, and any worker job or environment-lifetime override. Without `--batch`,
it runs batches in order and stops formatting at the first failed batch.
Pass `--batch N` to run only a specific 1-based validation batch:

```sh
scripts/validate-external-projects.sh \
  --files Mathlib/Combinatorics \
  --batch 2 \
  mathlib=https://github.com/leanprover-community/mathlib4.git
```

To resume an interrupted scratch validation, pass `--start-batch N` with
`--reuse-clone`. The validator keeps the existing clone and validates batch `N`
and every later batch. Add `--skip-initial-build` only when that same clone
already completed the clean pre-format build:

```sh
scripts/validate-external-projects.sh \
  --files Mathlib \
  --start-batch 34 \
  --reuse-clone \
  --skip-initial-build \
  --skip-final-build \
  mathlib=$HOME/work/lean-libs/mathlib4
```

Validation batches remain serial so a failure has one unambiguous stopping point.
Within each formatter invocation, worker batches run concurrently up to the configured
job limit. Each validation batch writes its formatter output to
`.scratch/external-validation/logs/PROJECT/batch-N.log` and updates the adjacent
`state` file with the running, passed, or failed batch, so interrupted runs can
be diagnosed and resumed without overlapping formatter invocations.

For formatter-only iteration, pass `--skip-final-build`. The initial clean build
still runs, but the validator omits the complete build after the last successful
or first failing formatter batch:

```sh
scripts/validate-external-projects.sh \
  --files Mathlib \
  --skip-final-build \
  mathlib=$HOME/work/lean-libs/mathlib4
```

Clones are created under `.scratch/external-validation`; `--reuse-clone` requires
the corresponding existing clone there. Set
`LEANFMT_VALIDATION_DIR` to use another directory,
`LEANFMT_VALIDATION_SKIP_CACHE=1` to build without downloading caches,
`LEANFMT_VALIDATION_FILE_PATTERN` to change the default file selector, or
`LEANFMT_VALIDATION_BATCH_SIZE` to change the validation batch size.
`LEANFMT_VALIDATION_ENVIRONMENTS_PER_WORKER` passes
`--environments-per-worker` to leanfmt to override the maximum exact
environments loaded during one worker's lifetime.
`LEANFMT_VALIDATION_FORMATTER_JOBS` passes `--jobs` to limit concurrent workers;
default-environment work uses the machine's hardware concurrency, while the automatic
imported-environment default is capped at two. Multi-file package formatter
invocations first process files that parse in leanfmt's default Lean environment, then
process files that need imported syntax in workers running under the target package's
`lake env`. Imported files are grouped by exact normalized import header. A group is
never split across workers, even when it contains many files. Environment groups are
balanced into lifetime-bounded batches and fed through a work-conserving concurrent
queue.
Each worker retains
only its most recent Lean-created environment, so adjacent identical headers reuse one
environment without a general LRU. It also reuses Lean's opaque state after an
identical first direct import and lets Lean extend and finalize that state for the
remaining imports. Worker output is buffered independently and emitted in batch order
after all workers complete, preventing concurrent diagnostics from interleaving.
The import-prefix cache is bounded by `--env-cache-size`. Files with a `module` header use
exported `.olean` data; scripts use private data, matching Lean's frontend. Lean itself
computes every transitive import, IR phase, initializer, and persistent extension;
leanfmt does not derive environments from a superset. An imported worker handles at
most 16 exact environments by default. Restarting it bounds Lean runtime state outside
the explicit caches. Lowering the worker-job count reduces peak memory; changing the
environment limit trades process setup time for each process's lifetime and retained
state. Setting
`--env-cache-size 0` disables prefix reuse and uses Lean's direct importer when a new
exact environment is required. The immediately preceding exact environment remains
available for files with an identical header. This direct path is
useful when checking compatibility with a new Lean release. Set
`LEANFMT_VALIDATION_LINE_WIDTH=N` to pass a project-specific line width to every
formatter invocation.

Imported environments can dominate both runtime and memory. Compare one and two
workers on the target machine with
`LEANFMT_VALIDATION_FORMATTER_JOBS=1` and
`LEANFMT_VALIDATION_FORMATTER_JOBS=2`. Lean's own memory ceiling is a soft,
per-process runtime check rather than a total budget for all workers, so worker count
is the reliable control for avoiding system-wide memory pressure.

For example, mathlib and CSLib can be validated at their 100-column convention
while continuing to use fresh scratch clones:

```sh
LEANFMT_VALIDATION_LINE_WIDTH=100 scripts/validate-external-projects.sh \
  --files Mathlib \
  mathlib=$HOME/work/lean-libs/mathlib4
LEANFMT_VALIDATION_LINE_WIDTH=100 scripts/validate-external-projects.sh \
  cslib=$HOME/work/lean-libs/cslib
```

The script stops formatting at the first failing validation batch, runs the one
post-format build unless `--skip-final-build` was passed, and exits with a nonzero
status if any executed phase failed. Each phase and the final summary include elapsed
wall-clock time. Build-cache retrieval is an optional optimization:
repositories without a `cache` executable are reported as skipped rather than
failed.
