# Lean of the Mathematical Commons

Source-linked Lean 4 formalizations of classical mathematics, beginning with
Emmy Noether. The library separates existing Mathlib results, source-shaped
packaging, completed local proofs, and open historical targets. It does not
claim that every paper with a module is completely formalized.

**Start here:** [Noether module guide](docs/noether/README.md) ·
[Build and verification](BUILDING.md) · [Contributing](CONTRIBUTING.md)

## Use the library

The project uses Lean `4.31.0` and the committed Mathlib lock at
`fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`. With elan installed:

```sh
lake exe cache get
lake build MathematicalCommons
```

Import the whole library with `import MathematicalCommons`, or select a module:

```lean
import MathematicalCommons.Noether.ModularInvariants1926
import MathematicalCommons.Noether.Idealtheorie1921
import MathematicalCommons.Noether.EliminationIdealTheorySurvey1924
```

Keep `lake-manifest.json`; do not run `lake update` as part of reproduction.
For a serial fresh-source build, axiom reports and a machine-readable inventory,
follow [BUILDING.md](BUILDING.md). Ordinary `lake build` is not itself an axiom audit.

## What is available

The [module guide](docs/noether/README.md) explains the scope of the reusable
invariant-theory, ideal-theory, generic-zero, Dedekind and noncommutative-algebra
results. The larger Hentzelt–Noether development includes substantial coordinate,
localization, regular-division and Smith-module infrastructure. Its later
historical resultant identifications and witness constructions remain explicit
open targets; helper counts are not paper-completion counts.

The recorded inventory at the **29 August 2026 checkpoint** is:

| Measure | Recorded count |
| --- | ---: |
| Direct imports in the Noether umbrella | 55 |
| Local modules including both umbrellas | 57 |
| Indexed work packets | 43 |
| Partially audited / completely audited works | 21 / 0 |
| Inventoried claim or target rows | 343 |
| Available/completed rows in that inventory | 154 |
| Of those, locally completed content rows | 59 |
| Open inventoried rows | 189 |

These are different units. A claim row can cover several declarations; locally
completed formal content is not a claim of mathematical novelty. The 154 rows
include 95 exact/modern Mathlib-coverage rows. See the dated
[coverage snapshot](artifacts/coordination/noether-coverage-snapshot-20260829.json)
for its classifications and limitations. Generate counts from the **current
checkout**, rather than relying on this historical table, with:

```sh
python3 scripts/noether_check.py
```

## Source, scope and evidence

[Paper inventory](docs/noether/paper-inventory.md) ·
[Source-to-declaration ledger](metadata/noether-theorems.tsv) ·
[Mathlib coverage and gaps](docs/noether/mathlib-coverage.md) ·
[Controlled-source reference](sources/noether/CANON_REFERENCE.json)

Formal proof validates the stated proposition, not the completeness of a paper,
a transcription, or a translation. Historical source discrepancies stay in the
critical apparatus; they are not silently repaired by changing the source text.
Attribution to joint authors and external Lean contributors is retained.

The original detailed README is preserved byte for byte as
[the 29 August checkpoint narrative](README.checkpoint-20260829.md). It records
historical build chains and local archive paths, not the current build status.
[CHANGELOG.md](CHANGELOG.md), existing receipts and release metadata remain intact.
Current-source CI writes a separate artifact with the checked commit, source
hashes, logs, and explicit axiom-report coverage. It does not rewrite old receipts.

## License and citation

See [LICENSE](LICENSE) (Apache-2.0), [CITATION.cff](CITATION.cff), and the attribution
notes in individual source files. For a precise result, cite its source locator,
Lean declaration, repository commit and corresponding verification evidence.
