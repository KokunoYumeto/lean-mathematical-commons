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
| Emmy Noether | active pilot | extend P22's completed cutoff-one equation-(33) witness through the later Smith stages, normalize the historical `E^(i)`, and prove the parallel `R^(i)` product/resultant half of equation (34); identify the freely adjoined `ζ` tail with the historical unbounded module; determinant norm/resultant identification and choice independence; Noetherian primary decomposition; remaining P25 function-field refinements; integral Plücker/Fischer layers | [DOI 10.5281/zenodo.20412587](https://doi.org/10.5281/zenodo.20412587) |
| Ernst Steinitz | deposited anchor only | field-theory paper inventory and algebraic-closure coverage | [DOI 10.5281/zenodo.20616988](https://doi.org/10.5281/zenodo.20616988) |
| J. J. Sylvester | queued | invariant/matrix/combinatorial paper inventory | [DOI 10.5281/zenodo.20520692](https://doi.org/10.5281/zenodo.20520692) |
| Hellmuth Kneser | queued | quadratic-form/topology/geometry paper inventory | [DOI 10.5281/zenodo.20836971](https://doi.org/10.5281/zenodo.20836971) |
| Paul Gordan | scaffold queued | use controlled TeX to support the invariant-theory dependency chain | [DOI 10.5281/zenodo.20616260](https://doi.org/10.5281/zenodo.20616260) |
| Heinrich Weber | deposited anchor only | acquire and audit a controlled paper corpus before promoting the cubic sidecar beyond an index entry | [DOI 10.5281/zenodo.21129946](https://doi.org/10.5281/zenodo.21129946) |
| Camille Jordan | deposited anchor only | acquire and audit a controlled paper corpus before promoting the affine-group sidecar beyond an index entry | [DOI 10.5281/zenodo.21129946](https://doi.org/10.5281/zenodo.21129946) |

Historical source editions remain centrally discoverable through
[modern-latex-manuscripts](https://github.com/KokunoYumeto/modern-latex-manuscripts).
This companion repository owns Lean declarations, Mathlib mapping, build
evidence, and formalization-specific QA only.

## Emmy Noether pilot

- [Paper inventory](noether/paper-inventory.md): all 43 numbered work packets,
  source spans, authorship roles, and canon-QA states.
- [Mathlib coverage](noether/mathlib-coverage.md): readable declaration audit.
- [External Lean discovery and publication front door](noether/external-lean-discovery-and-publication.md):
  content-level audit of four initial and three follow-up commit-pinned
  Internet Lean files, the two attributed P40 adaptations, the independently
  written P11 absorption, the existing Zenodo concept lineage, a proposed
  author-facing repository, and the priority ranking for the remaining work.
- [Machine-readable coverage snapshot](../artifacts/coordination/noether-coverage-snapshot-20260829.json):
  21 of 43 works partially audited over 7,694 controlled-source lines; 154 of
  343 inventoried units completed or available; 59 newly completed local rows,
  of which 58 are locally original and one is an externally attributed
  promoted gap; and explicitly caveated 17–22% availability and 6–8% local-
  completion whole-corpus planning estimates.
- [1918 prescribed-group claim route](../metadata/topic-literature-route-noether-p11-prescribed-group.json):
  ten source claims, three green full-symmetric-group support declarations,
  exact Lüroth infrastructure, and the still-open fixed-field,
  minimal-basis/parameterization, singular-locus, reduction, Castelnuovo, and
  cyclotomic cases.
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
  cutoff-one cyclic-quotient/determinant instance, the freely adjoined arbitrary
  and countable Finsupp `ζ` tails with coefficient `1` and common-tail
  cancellation, the scalar-colon interpretation after equation (24), its
  unconditional one-step principal quotient, and the exact whole-ground
  quotient as an infimum of the remaining principal coefficient ideals. It
  also types Satz II's reciprocal module-valued ideal quotient and proves
  `G₁* = M₁*/(eᵢ)` for the actual localized pair, alongside the scalar-colon
  identity `M₁*/G₁* = (eᵢ)`. The opening finite localized kernel of Satz VIII
  is unconditional in intrinsic form: the quotient annihilator is `⋂ᵢ(eᵢ)`,
  and for `D = ∏ᵢeᵢ` it proves `(D) ≤ A`, `A^ρ ≤ (D)`, both generator
  divisibilities, and radical equality. Under the explicit greatest-divisor
  hypothesis it now recovers `A = (eᵢ)`, `eᵢ ∣ D`, `D ∣ eᵢ^ρ`, and the
  actual localized radical/vanishing bridge. The selected localized greatest
  coefficient now has a nonzero integral numerator. `FirstSmithEquation33Bridge`
  uses regular division to lift its
  bounded action to every member of the cutoff-one ground ideal and produces
  the full `HasEquation33Witness I 1` with a genuine cutoff-two denominator.
  Four `NEW_PACKAGING` declarations then clear its localized divisibility into
  the finite selected-coefficient product and produce a compatible nonzero
  integral product numerator whose lift retains that witness. Local cutoff `1`
  is source stage `i = 2`. Removing content now yields primitive nonzero
  integral representatives for the selected coefficient and product, with
  `e ∣ r`, `r ∣ e ^ ρ`, and both equation-(33) witnesses preserved. These are
  still selected proxies, not historical `E^(2)` or `R^(2)`, a module norm, gcd
  of maximal minors, or historical resultant; they are not canonical or
  choice-independent. The selected-basis transition determinant is now defined
  over the localized ground-to-denominator equivalence, proved equal to the
  finite selected-coefficient product, and controlled up to association under a
  basis change; the primitive product proxy is associated with it after
  localization. This remains distinct from historical `R^(2)` and its norm,
  minor-gcd, normalization, and choice-independence bridges. A new ten-
  declaration finite-matrix scaffold defines selected `k`-minors and the ideal
  they span, with generator, repeated-row/column, zero-matrix, and degree-zero
  lemmas. It is explicitly `NEW_PACKAGING`, not yet a Fitting ideal,
  Cauchy--Binet invariance result, maximal-minor gcd, module norm, or historical
  resultant.
  Equation (33)'s one-stage Noetherian descent is formalized generally, and a
  supplied witness family is iterated
  through arbitrary finite windows to prove `g_n = I`, the conditional
  `E`-product half of equation (34), and its tail-window endpoint. Extending the
  construction through the later stages, historical/canonical primitive-form
  identification and choice independence, and the parallel
  `R`-product/resultant half remain open. The
  free-tail model is not yet identified with a separately constructed/localized
  historical unbounded module; there is no canonical coefficient ordering,
  resultant identification, or infinite determinant. Current P22 accounting is
  576 declarations across the base and 38 support modules. The integrated graph
  has 53 direct Noether imports, and both fresh serial umbrella receipts are
  green. That P22 checkpoint pins all 53 direct Noether imports and both umbrellas in the
  [55-target checkpoint](../artifacts/build/module-graph-checkpoint-20260829T2141556003305-de54d554.json),
  which chains the preceding 54-target checkpoint. P40 and P11 subsequently
  bring the global graph to 55 direct Noether imports plus both umbrellas in
  the current
  [57-target checkpoint](../artifacts/build/module-graph-checkpoint-20260829T2327308948138-d815b8e6.json).
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
- [1933 noncommutative-algebra P40 module](../MathematicalCommons/Noether/NoncommutativeAlgebras1933.lean):
  green attributed adaptations of QICLean's arbitrary-field full-matrix
  automorphism case and TauCeti's real-quaternion embedding-conjugacy case.
  Blackfeather's Jacobson–Noether result is already in Mathlib; TauCeti's broad
  central-source theorem was inspected without copying its dependency cluster,
  and Noether's full simple-subring statement remains open.
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
