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
lake exe fmt --line-width 100 --recursive Mathlib
```

Directory arguments include directly contained `.lean` files. Pass
`--recursive` or `-r` to include nested directories. Hidden files and
directories discovered inside directory arguments are skipped by default.
Explicitly supplied hidden paths are still processed. Pass `--include-hidden`
to include hidden descendants during directory traversal. LeanFmt uses a
90-character line limit by default; pass `--line-width N` when a project uses a
different convention.

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
- [Comparison](docs/comparison.md) compares LeanFmt's style, architecture, and workflow
  with Lean's standard-library guide and pretty-lean.
