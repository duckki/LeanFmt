# LeanFmt repository guide

This file is the repository-local operational memory for agents working on
LeanFmt. Run commands from the repository root. The detailed documentation
linked below remains the source of truth when this summary and the code diverge.

## Repository layout

- `LeanFmt.lean` is the public library entry point.
- `LeanFmt/SyntaxTree.lean` parses Lean source into the lossless tree and performs
  syntax regrouping.
- `LeanFmt/Formatter.lean` exposes the formatting API and drives convergence.
- `LeanFmt/Formatter/SpaceRules.lean` owns horizontal token spacing.
- `LeanFmt/Formatter/LineBreakRules.lean` owns syntax-specific break rules and
  the complete rule dispatch table.
- `LeanFmt/Formatter/Renderer.lean` owns layout state, fit checks, indentation,
  and text emission. Keep syntax-specific decisions out of the renderer.
- `LeanFmt/Formatter/Diagnostics.lean` checks code preservation, actionable line
  overflow, and missing rules; `Trace.lean` supports renderer debugging.
- `LeanFmt/Cli.lean` implements the public `fmt` executable.
- `LeanFmt/LeanEnvironment.lean` is the narrow adapter to Lean's exact
  header/import-environment APIs; worker batching and caches stay in
  `LeanFmt/Driver/`. Keep direct and incrementally reused import paths equivalent;
  the direct path is the compatibility fallback for Lean upgrades.
- `LeanFmt/Tests/Suite.lean` contains the unit-style suites executed through
  `#eval`; `LeanFmt/Tests/Cli.lean` implements the fixture/test CLI and
  `LeanFmt/Tests/Main.lean` is its executable entry point.
- `Tests/Fixtures/<category>/*.leanfmt` contain input above the separator and
  generated expected output below it. Do not hand-edit the generated half.
- `scripts/validate-external-projects.sh` validates the formatter against fresh
  clones of external Lean projects.
- `tools/linter/` is a separate development-only Lake package that pins
  Batteries and runs environment linters without adding Batteries to LeanFmt's
  released dependency graph.
- `lakefile.toml`, `lake-manifest.json`, and `lean-toolchain` define the released
  package, executables, and canonical Lean version. The root package depends
  only on Lean. `.lake/` is generated.
- `.scratch/external-validation/` contains disposable external-validation clones
  and must remain untracked.

## Documentation layout

- `README.md` is the user-facing overview, installation/usage guide, project
  status, and external-validation entry point.
- `docs/design.md` is the normative formatting style and examples.
- `docs/architecture.md` documents pipeline boundaries, invariants, tree shape,
  rules, renderer behavior, and diagnostics.
- `docs/development.md` is the contributor guide for building, tests, fixtures,
  tracing, profiling, and adding rules.

Update the relevant document when a change alters user-visible formatting,
module responsibilities, diagnostics, CLI behavior, or validation commands.

## Required branch and PR validation

Every branch or PR should pass this review gate. Run focused checks while
developing, then run the complete sequence before requesting review.

1. Build, run the unit-style suite, and run the development linter:

   ```sh
   lake build
   lake test
   make lint
   ```

2. Regenerate every fixture after an intentional formatter change:

   ```sh
   lake exe fmt-test --update-fixture Tests/Fixtures/*/*.leanfmt
   ```

   Review `git diff -- Tests/Fixtures` immediately. Confirm each generated
   output change is intended, structure-preserving, and represented by focused
   coverage. Never accept fixture churn merely because it was generated.

3. Self-format all formatter and test sources while running the exception and
   idempotency checks:

   ```sh
   lake exe fmt --check-exception --check-idempotent \
     -r LeanFmt
   ```

   This invocation writes formatting changes only for files without exceptions.
   `--check-exception` checks non-whitespace code preservation, actionable line
   overflow, and missing rule dispatch; `--check-idempotent` performs a second
   formatting pass. Review `git diff -- LeanFmt` after it runs, including
   mechanically generated changes.

4. If fixture or self-formatting output changed Lean sources, rerun `lake build`
   and `lake test`. Then run the final dry checks:

   ```sh
   lake exe fmt-test --update-fixture --check Tests/Fixtures/*/*.leanfmt
   lake exe fmt --check --check-exception --check-idempotent \
     -r LeanFmt
   git diff --check
   ```

   With diagnostic options present, `--check` is a dry-run switch: files that
   merely need formatting are reported, while diagnostic exceptions determine
   failure. The final run should report neither formatting drift nor exceptions.

Summarize the build, test, fixture, preservation, overflow, missing-rule, and
idempotency results for review. Do not commit generated or handwritten changes
until the reviewer explicitly asks for a commit.

## Short-term external-validation goal

The current short-term goal is for both CSLib and mathlib to pass the complete
external formatter validation. The validation script requires at least one
explicit Git repository argument and has no preset targets:

```sh
scripts/validate-external-projects.sh \
  mathlib=https://github.com/leanprover-community/mathlib4.git
```

For an iterative single-project run, pass `GIT_REPO` or `NAME=GIT_REPO`; the
source can be a local path or any clone source accepted by `git clone`, and it is
cloned into a fresh scratch checkout unless `--reuse-clone` is passed. Pass
`--files FILE_SELECTOR` or
append `::FILE_SELECTOR` to one project spec to validate a tracked-file subset.
When the selector names a tracked directory, every tracked `.lean` file under
that directory is included:

```sh
scripts/validate-external-projects.sh \
  --files Mathlib/Combinatorics \
  mathlib=https://github.com/leanprover-community/mathlib4.git
```

Set `LEANFMT_VALIDATION_LINE_WIDTH=100` when validating mathlib or CSLib against
their 100-column convention:

```sh
LEANFMT_VALIDATION_LINE_WIDTH=100 scripts/validate-external-projects.sh \
  --files Mathlib mathlib=$HOME/work/lean-libs/mathlib4
LEANFMT_VALIDATION_LINE_WIDTH=100 scripts/validate-external-projects.sh \
  cslib=$HOME/work/lean-libs/cslib
```

For each project the script builds LeanFmt, creates a fresh clone under
`.scratch/external-validation/`, optionally downloads the project's Lake cache,
and runs one complete build before formatting. It then formats each file batch
directly with `--check-exception --check-idempotent` under the target project's
`lake env` until all batches pass or the first diagnostic failure occurs. It then
runs one complete build over every candidate written through that point. This
post-format build also runs after a formatter failure; after both results are
reported, validation stops. It times every phase and returns failure when any
required phase fails. A missing build-cache executable is only an optional-phase
skip. Pass `--skip-final-build` during formatter-only iteration to omit the
post-format build while retaining the initial clean build. To resume an existing
scratch clone after a successful batch, combine `--start-batch N`,
`--reuse-clone`, and `--skip-initial-build`; the validator then continues from
batch `N` without recloning or repeating the completed pre-format build.
Formatter workers run serially. Per-batch output and the last batch state are
persisted under `.scratch/external-validation/logs/PROJECT/`.

Review external changes and diagnostics in the scratch clone. Treat code changes,
non-idempotence, missing rules, actionable overflow, and either build failure as
formatter issues to investigate. Convert each issue into a focused internal test
or fixture and a formatter fix; do not make the scratch clone the source of the
fix. Rerun the affected project until clean, then rerun the explicit CSLib/mathlib
pair to close the short-term goal.
