# Noether: module guide and completion boundaries

This guide identifies entry points. It is not a claim that every theorem in the
corresponding paper is formalized. Public declarations keep their existing
namespaces; importing one focused module avoids importing the whole programme.

## Useful entry points

| Module under `MathematicalCommons.Noether` | Proved or packaged scope | Boundary to retain |
| --- | --- | --- |
| [`ModularInvariants1926`](../../MathematicalCommons/Noether/ModularInvariants1926.lean) | Fixed-ring finite generation and intermediate-subalgebra finite generation for finite group actions on finite-type commutative algebras over Noetherian bases. | No characteristic-zero requirement, but no particular group's explicit invariant generators or Molien series is supplied. |
| [`Idealtheorie1921`](../../MathematicalCommons/Noether/Idealtheorie1921.lean) | Primary/irreducible ideal packages, associated-prime uniqueness and positive-exponent clauses. | Distinguish Mathlib wrappers from locally assembled packages; this is not a complete paper audit. |
| [`EliminationIdealTheorySurvey1924`](../../MathematicalCommons/Noether/EliminationIdealTheorySurvey1924.lean) | The generic zero in a prime coordinate ring's fraction field, its exact evaluation kernel, field generation and transcendence-degree bounds. | The strict finite-coordinate inequality requires a **nonzero** prime ideal. |
| [`AbstractIdealTheory1924`](../../MathematicalCommons/Noether/AbstractIdealTheory1924.lean) and [`DedekindTheory1927`](../../MathematicalCommons/Noether/DedekindTheory1927.lean) | Dedekind-domain characterization and the Artinian-nonzero-quotient/dimension-one bridge. | Preserve the declared domain/Noetherian hypotheses and distinguish the source's larger programme. |
| [`EquationsWithPrescribedGroup1918`](../../MathematicalCommons/Noether/EquationsWithPrescribedGroup1918.lean) | Full symmetric invariant-ring and abstract fraction-ring packages. | The arbitrary prescribed-subgroup fixed-field and parameterization claims remain separate. |
| [`NoncommutativeAlgebras1933`](../../MathematicalCommons/Noether/NoncommutativeAlgebras1933.lean) | Attributed full-matrix and real-quaternion inner-automorphism packages. | Not the full simple-subring theorem. External contributor attribution stays with the source. |

The joint Noether–Schmeidler module is under
[`MathematicalCommons.NoetherSchmeidler`](../../MathematicalCommons/NoetherSchmeidler/NoncommutativeModules1920.lean).
This is a joint-author namespace, not an orphan or a duplicate to rename away.

## Hentzelt–Noether: a substantial development, not a completed resultant theory

The [1923 base module](../../MathematicalCommons/Noether/PolynomialIdealsAndResultants1923.lean)
and its [support modules](../../MathematicalCommons/Noether/PolynomialIdealsAndResultants1923/)
cover source-linked coordinate transformations, localization, regular division,
finite bounded quotients, saturation, Smith-module decompositions, annihilator
and selected-product bounds, and conditional stage iteration.

The remaining identification layer is mathematically specific. The selected
coefficient product or transition determinant is not automatically Hentzelt's
historical resultant, module norm, or canonical primitive form. Likewise,
iteration given a later-stage witness family does not construct that family.
The independently adjoined tail must not be silently identified with a separately
constructed historical unbounded module. Those are further theorems, not reasons
to discard the completed supporting results.

Use the [detailed source crosswalk](hentzelt-polynomial-ideals-resultants-1923.md)
and [claim ledger](../../metadata/noether-theorems.tsv) before selecting a next
target. In particular, a `NEW_PACKAGING` lemma can be useful infrastructure without
closing a `GAP_CANDIDATE` historical claim.

## Reading the inventory

[`metadata/noether-works.tsv`](../../metadata/noether-works.tsv) inventories work
packets, while [`metadata/noether-theorems.tsv`](../../metadata/noether-theorems.tsv)
inventories source claims or proof packages. Neither is a list of discoveries.
`MATHLIB_EXACT`, `MATHLIB_MODERN_FORM`, `NEW_PACKAGING`, `FORMALIZED_GAP`,
`GAP_CANDIDATE`, `BLOCKED_SOURCE`, and `DEFERRED_INFRASTRUCTURE` answer different
questions. Read them together with `local_contribution`, `build_status`, the
source locator and the limitations column. A successful support build does not
reclassify its larger open target as complete.

The [dated coverage snapshot](../../artifacts/coordination/noether-coverage-snapshot-20260829.json)
reports 21 partially audited works and no complete paper audit. Generate current
raw counts with `python3 scripts/noether_check.py` from the repository root.
The script does not automatically reinterpret the historical status labels or
change the original-source transcription.

## Further navigation

[All 43 work packets](paper-inventory.md) · [Mathlib coverage](mathlib-coverage.md) ·
[External Lean sources and attribution](external-lean-discovery-and-publication.md) ·
[Build and verification](../../BUILDING.md) · [Contribution rules](../../CONTRIBUTING.md)
