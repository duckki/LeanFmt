# leanfmt

leanfmt is a structure-preserving code formatter for Lean. It parses complete
Lean files with Lean's own parser, preserves source tokens and comments, and
formats declarations and expressions through the `fmt` executable.

leanfmt favors layouts that expose the structure of Lean code. In particular,
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

## Add leanfmt to a Lake package

Add the Git dependency to `lakefile.toml`:

```toml
[[require]]
name = "leanfmt"
git = "https://github.com/duckki/leanfmt.git"
rev = "v0.2.5"
```

Preserve the package's Lean version when resolving the dependency:

```sh
lake update --keep-toolchain
```

leanfmt uses one source release across its supported Lean versions and tests the
current toolchain and previous minor versions in CI. `--keep-toolchain` prevents
Lake from replacing an older project's toolchain with the version recorded by
leanfmt. leanfmt is then built with the project's selected Lean version, which is
important because it loads that project's parser extensions and imported
environments.

Projects that do not want leanfmt in their published dependency graph may place
the requirement in a separate development-tool Lake package instead. That tool
package should also depend on the project by a local path so leanfmt can load the
project's dependencies and parser extensions.

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
to include hidden descendants during directory traversal. leanfmt uses a
90-character line limit by default; pass `--line-width N` when a project uses a
different convention.

To preserve the next complete syntax node exactly, put `-- leanfmt: off next`
immediately before it. The marker works for top-level commands and nested terms:

```lean
-- leanfmt: off next
def handAligned   :   Nat:=
       1
```

```lean
def handAlignedFunction : Nat → Nat :=
  -- leanfmt: off next
  fun n =>
      n + 1
```

To preserve a manual source region exactly, wrap it in line comments:

```lean
-- leanfmt: off
def handAligned   :   Nat:=
       1
-- leanfmt: on
```

leanfmt formats parseable chunks outside the ignored region and keeps the marker
lines and enclosed lines unchanged, apart from the command's normal line-ending
normalization.

To verify formatting without changing files, use `--check`:

```sh
lake exe fmt --check --recursive LeanFmt
```

The command exits nonzero if a file would change or cannot be formatted, making
it suitable for CI.

## Status

leanfmt is under active development. Review formatting changes before applying
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
- [Comparison](docs/comparison.md) compares leanfmt's style, architecture, and workflow
  with Lean's standard-library guide and pretty-lean.

## License

leanfmt is released under the [MIT License](LICENSE).
