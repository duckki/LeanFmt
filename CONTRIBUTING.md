# Contributing to LeanFmt

LeanFmt follows the Lean community's maintenance conventions used by mathlib and
CSLib, adapted for a formatter that intentionally depends only on Lean and
Batteries.

## Code standards

- Treat compiler warnings as errors in review and CI.
- Add documentation comments to new public APIs and explain non-obvious invariants.
- Keep imports narrow and module responsibilities aligned with
  [the architecture](docs/architecture.md).
- Add focused tests or fixtures for behavior changes. Do not hand-edit the
  generated half of a fixture.
- Keep shell scripts clean under ShellCheck at warning severity or higher.
- Use a conventional PR title such as `feat: ...`, `fix: ...`, `doc: ...`,
  `style: ...`, `refactor: ...`, `test: ...`, `chore: ...`, `perf: ...`, or
  `ci: ...`.

## Local review gate

Run the standard maintenance checks with:

```sh
make check
make shellcheck
```

`make check` builds and tests with warnings treated as errors, runs the Batteries
environment linters, checks generated fixtures, verifies code preservation and
formatter idempotency, and rejects whitespace errors.

Existing environment-linter debt is recorded in `scripts/nolints.json`. Do not
add entries merely to make a change pass. Fix new findings, and remove stale
entries after fixing old findings with:

```sh
lake lint -- --update LeanFmt.Cli
```

If formatter output changes intentionally, regenerate fixtures first and review
the resulting diff:

```sh
lake exe fmt-test --update-fixture Tests/Fixtures/*/*.leanfmt
git diff -- Tests/Fixtures
```

See [the development guide](docs/development.md) for tracing, profiling, and the
full formatter-specific workflow. Prepare an uncommitted, validated slice for
review; commit only after approval.
