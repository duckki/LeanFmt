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
- `Tests/LeanFmt.lean` contains the unit-style suites executed through `#eval`;
  `Tests/TestCli.lean` and `Tests/Cli.lean` implement the fixture/test executable.
- `Tests/Fixtures/<category>/*.leanfmt` contain input above the separator and
  generated expected output below it. Do not hand-edit the generated half.
- `scripts/validate-external-projects.sh` validates the formatter against fresh
  clones of external Lean projects.
- `lakefile.toml`, `lake-manifest.json`, and `lean-toolchain` define the package,
  executables, dependencies, and pinned Lean version. `.lake/` is generated.
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

1. Build and run the unit-style suite:

   ```sh
   lake build
   lake test
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
     -r LeanFmt Tests/*.lean
   ```

   This invocation writes formatting changes only for files without exceptions.
   `--check-exception` checks non-whitespace code preservation, actionable line
   overflow, and missing rule dispatch; `--check-idempotent` performs a second
   formatting pass. Review `git diff -- LeanFmt Tests` after it runs, including
   mechanically generated changes.

4. If fixture or self-formatting output changed Lean sources, rerun `lake build`
   and `lake test`. Then run the final dry checks:

   ```sh
   lake exe fmt-test --update-fixture --check Tests/Fixtures/*/*.leanfmt
   lake exe fmt --check --check-exception --check-idempotent \
     -r LeanFmt Tests/*.lean
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
external formatter validation. Run the default pair with:

```sh
scripts/validate-external-projects.sh
```

For an iterative single-project run, pass `NAME=GIT_URL_OR_PATH`; a local source
is still cloned into a fresh scratch checkout:

```sh
scripts/validate-external-projects.sh \
  cslib=$HOME/work/lean-libs/cslib
scripts/validate-external-projects.sh \
  mathlib=https://github.com/leanprover-community/mathlib4.git
```

For each project the script builds LeanFmt, creates a fresh shallow clone under
`.scratch/external-validation/`, optionally downloads the project's Lake cache,
builds the project before formatting, formats every tracked `.lean` file with
`--check-exception --check-idempotent`, and builds the formatted project again.
It times every phase, continues after individual failures, and returns failure
when any required phase fails. A missing build-cache executable is only an
optional-phase skip.

Review external changes and diagnostics in the scratch clone. Treat code changes,
non-idempotence, missing rules, actionable overflow, and either build failure as
formatter issues to investigate. Convert each issue into a focused internal test
or fixture and a formatter fix; do not make the scratch clone the source of the
fix. Rerun the affected project until clean, then rerun the default CSLib/mathlib
pair to close the short-term goal.
