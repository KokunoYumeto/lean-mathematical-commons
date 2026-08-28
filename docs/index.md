# Lean of the Mathematical Commons

Canonical public repository:
[KokunoYumeto/lean-mathematical-commons](https://github.com/KokunoYumeto/lean-mathematical-commons).

This is the central index for source-linked Lean work across the local
classical-mathematics corpora. It points to corpora; it does not duplicate
their large source trees. The machine-readable version is
[`metadata/authors.tsv`](../metadata/authors.tsv).

## Status vocabulary

- **active pilot**: paper and theorem ledgers exist and promoted Lean code has
  reproducible build evidence;
- **deposited anchor only**: an earlier public sidecar identifies at least one
  Mathlib result, but no complete paper audit exists here;
- **scaffold queued**: useful controlled source material exists, but formal
  claims have not been promoted;
- **queued**: corpus is known and indexed, with no asserted Mathlib coverage.

These labels describe project work, not mathematical importance and not the
novelty of a theorem.

## Authors

| Author | State | Next formalization lane | Corpus record |
|---|---|---|---|
| Emmy Noether | active pilot | extend P22's localized finite equation-(24) instance to divisibility ordering, the infinite `ζ` tail/unit factors, determinant norm/resultant identification, primitive normalization and choice independence, then iterate later stages and compatible zeros; Noetherian primary decomposition; remaining P25 function-field refinements; integral Plücker/Fischer layers | [DOI 10.5281/zenodo.20412587](https://doi.org/10.5281/zenodo.20412587) |
| Ernst Steinitz | deposited anchor only | field-theory paper inventory and algebraic-closure coverage | [DOI 10.5281/zenodo.20616988](https://doi.org/10.5281/zenodo.20616988) |
| J. J. Sylvester | queued | invariant/matrix/combinatorial paper inventory | [DOI 10.5281/zenodo.20520692](https://doi.org/10.5281/zenodo.20520692) |
| Hellmuth Kneser | queued | quadratic-form/topology/geometry paper inventory | [DOI 10.5281/zenodo.20836971](https://doi.org/10.5281/zenodo.20836971) |
| Paul Gordan | scaffold queued | use controlled TeX to support the invariant-theory dependency chain | [DOI 10.5281/zenodo.20616260](https://doi.org/10.5281/zenodo.20616260) |

Historical source editions remain centrally discoverable through
[modern-latex-manuscripts](https://github.com/KokunoYumeto/modern-latex-manuscripts).
This companion repository owns Lean declarations, Mathlib mapping, build
evidence, and formalization-specific QA only.

## Emmy Noether pilot

- [Paper inventory](noether/paper-inventory.md): all 43 numbered work packets,
  source spans, authorship roles, and canon-QA states.
- [Mathlib coverage](noether/mathlib-coverage.md): readable declaration audit.
- [1918 variational dependency map](noether/variational-1918.md): exact result
  inventory, source qualifications, Mathlib anchors, and missing foundations.
- [1919 integral-invariant map](noether/integral-invariants-1919.md): binary
  forms, determinant generation, multisymmetry, Plücker relations, and
  straightening gaps.
- [1920 series-expansion map](noether/series-expansion-1920.md): relation
  ideals, Fischer projection, polar/Omega expansions, and authorial corrections.
- [1920 Noether–Schmeidler noncommutative-module map](noether/noncommutative-modules-1920.md):
  promoted quotient-product core, skew-ring Noetherianity, semisimple factors,
  and PDE gaps.
- [1921 Noether report on Hentzelt](noether/hentzelt-elimination-report-1921.md):
  attribution-sensitive resultant claims and source-blocked elimination
  semantics.
- [1923 Hentzelt--Noether polynomial ideals and resultants](noether/hentzelt-polynomial-ideals-resultants-1923.md):
  staged module/resultant definitions, Smith/norm coverage, the promoted
  relative and multivariate Dedekind--Mertens equation (17), the natural
  equation-(12) transform, literal stage multipliers, the completed two-sided
  Satz VI ground-ideal equality, Satz XI's exact basis, Satz XII's finite-zero
  substrate and Nullstellensatz corollary, characteristic-zero finite
  regularity specialization, equation-(12) homogeneous preservation and
  generator-level leading coefficients, equation-(21) regular division,
  equations-(22)--(23) finite coefficient vectors and internal ideal
  decomposition, the cutoff-one `ξ`/`ζ` coordinate-module quotient bridge, the
  exact line-13162 nonzero-scalar ground-module saturation and its
  torsion/equal-rank consequences, the source-faithful tower
  `P[x₃,…][x₂] → Frac(P[x₃,…])[x₂]` with exact localized saturation
  and `finrank`, a generic equation-(24) Smith package and its actual finite
  cutoff-one cyclic-quotient/determinant instance, and promoted Satz VIII
  support.
- [1922 absolute-irreducibility map](noether/absolute-irreducibility-1922.md):
  universal reducibility-form and specialization gaps, with proof components.
- [1922 formal-variational-calculus map](noether/formal-variational-calculus-1922.md):
  central equations, polarization, covariant derivatives, curvature, and the
  infrastructure boundary for Noether I and II.
- [1923 algebraic/differential-invariant map](noether/algebraic-differential-invariants-1923.md):
  Hilbert's five arithmetic steps, uniform radical powers, Reynolds gaps, and
  the differential reduction theorem.
- [1923 elimination/general-ideal-theory map](noether/elimination-ideal-theory-1923.md):
  successive Smith forms, primary components, dimension, and good-reduction
  gaps.
- [1924 elimination/ideal-theory survey map](noether/elimination-ideal-theory-survey-1924.md):
  root fields, primary decomposition, generic zeros, and the under-specified
  successive norm.
- [1924–1925 communications map](noether/communications-1924-1925.md):
  Dedekind characterization, Hilbert numbers, and semisimple group-character
  ideal theory.
- [1926 modular-invariant map](noether/modular-invariants-1926.md): fixed-ring
  finite generation, the Artin–Tate bridge, and remaining explicit generators.
- [1927 abstract Dedekind-theory map](noether/dedekind-theory-1927.md): the five
  axioms, ideal factorization, fractional ideals, finite length, and the
  promoted Artinian-quotient/dimension-one bridge.
- [1927 discriminant-theorem map](noether/discriminant-theorem-1927.md): finite
  algebras and orders, scalar extension, discriminants, localization, and
  ramification, including the pinned étale-descent axiom caveat.
- [`metadata/noether-theorems.tsv`](../metadata/noether-theorems.tsv):
  machine-readable theorem ledger.
- [`metadata/noether-canon-qa.tsv`](../metadata/noether-canon-qa.tsv): open
  source conflicts routed to the German canon owner.
- [`MathematicalCommons/Noether`](../MathematicalCommons/Noether): promoted Lean
  modules.
- [`artifacts/release/noether-pilot-0.1.0-dev`](../artifacts/release/noether-pilot-0.1.0-dev):
  independently verifiable local release candidate.

## Admission rule

An author or theorem does not become “formalized” merely because a wrapper was
written. A promoted theorem needs a controlled source locator, explicit modern
assumptions, a Mathlib classification, no `sorry`/`admit`, `#print axioms`
evidence, a one-thread RAM-bounded build receipt, and documented limitations.
German textual decisions remain with the separate canon owner.
