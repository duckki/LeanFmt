# LeanFmt

LeanFmt is a structure-preserving code formatter for Lean. It parses complete
Lean files with Lean's own parser, preserves source tokens and comments, and
formats declarations and expressions through the `fmt` executable.

LeanFmt favors layouts that expose the structure of Lean code. In particular,
leading operators connect continuation lines vertically while indentation shows
nested expressions.

## Formatting output

Before:

```lean
def parenthesizedConjunctionChain (schema : Schema) : Prop :=
  namesAreUnique (schema.allTypes.map TypeDefinition.name) ∧
    schema.objectType schema.queryType ∧
    (∀ typeDefinition, typeDefinition ∈ schema.types
      -> typeDefinitionWellFormed schema typeDefinition) ∧ (∀ typeName objectTypeName,
          objectTypeName ∈ schema.getPossibleTypes typeName
    -> schema.objectType objectTypeName)
```

After:

```lean
def parenthesizedConjunctionChain (schema : Schema) : Prop :=
  namesAreUnique (schema.allTypes.map TypeDefinition.name)
  ∧ schema.objectType schema.queryType
  ∧ (∀ typeDefinition,
      typeDefinition ∈ schema.types -> typeDefinitionWellFormed schema typeDefinition)
  ∧ (∀ typeName objectTypeName,
      objectTypeName ∈ schema.getPossibleTypes typeName
      -> schema.objectType objectTypeName)
```

Nested logical groups keep their local structure:

```lean
def leadingArrowExistentialApplicationWrap : Prop :=
  ∃ interfaceType,
    schema.lookupInterface interfaceName = some interfaceType
    ∧ ∀ interfaceField,
        interfaceField ∈ interfaceType.fields
        -> ∃ implementationField,
            Schema.lookupFieldDefinition implementationFields interfaceField.name
              = some implementationField
            ∧ fieldDefinitionImplements schema implementationField interfaceField
```

See the [formatting design](docs/design.md) for the complete rule descriptions
and more examples.

## Add LeanFmt to a Lake package

Add the Git dependency to `lakefile.toml`:

```toml
[[require]]
name = "leanfmt"
git = "https://github.com/duckki/leanfmt.git"
rev = "main"
```

Then format files or directories through Lake:

```sh
lake exe fmt LeanFmt/Formatter.lean
lake exe fmt LeanFmt
lake exe fmt --recursive LeanFmt
```

Directory arguments include directly contained `.lean` files. Pass
`--recursive` or `-r` to include nested directories.

To verify formatting without changing files, use `--check`:

```sh
lake exe fmt --check --recursive LeanFmt
```

The command exits nonzero if a file would change or cannot be formatted, making
it suitable for CI.

## Status

LeanFmt is under active development. Review formatting changes before applying
it broadly. Formatting is deliberately conservative: it changes whitespace,
keeps token text and order and preserves proof regions.

## Project documentation

- [Contributing](CONTRIBUTING.md) defines the code-quality standards and local review
  gate.
- [Design](docs/design.md) describes the style, philosophy, rules, and examples for Lean
  programmers considering the formatter.
- [Architecture](docs/architecture.md) explains the implementation decisions and division
  between the syntax tree, rules, and renderer.
- [Development](docs/development.md) covers building, testing, fixtures, tracing,
  profiling, validation, and contributing new rules.

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
scripts/validate-external-projects.sh graphql-lean=$HOME/work/apollo-graphql/graphql-lean
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
`LEANFMT_VALIDATION_BATCH_SIZE` to change the number of files passed to each formatter
invocation. The script continues after individual phase failures so it can report all
issues, then exits with a nonzero status if any phase failed. Each phase and the final
summary include elapsed wall-clock time. Build-cache retrieval is an optional
optimization: repositories without a `cache` executable are reported as skipped rather
than failed.
