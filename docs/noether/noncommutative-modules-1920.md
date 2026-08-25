# Noether–Schmeidler 1920: noncommutative modules

This is the source and Mathlib map for Emmy Noether and Werner Schmeidler,
*Moduln in nichtkommutativen Bereichen, insbesondere aus Differential- und
Differenzenausdrücken*. The joint attribution is essential and is retained in
the proposed Lean namespace.

## Controlled source and dictionary

- Work ID: **P17**; packet lines 10071–11214, displayed title at 10090–10095.
- Witness: `NOETH-DE-ED-0014`, SHA-256
  `EE226847656BC4D65EDDA9E9BF9BB1D25797C0C6D672D267D94A97FD88C7AD58`.
- `P` is an arbitrary commutative field at lines 10214–10232.
- `J` is an assumed associative noncommutative polynomial/operator ring. Its
  variables commute with one another; from §6 the triangular coefficient rule
  is `ξᵢ a = aᵢ ξᵢ + bᵢ` with `aᵢ ≠ 0` (10225–10232, 10457–10462).
- A source “rechtsseitiger Modul” is additive and closed under expressions
  `F M`, hence under multiplication from the left. It maps to `Submodule R R`
  in Mathlib's left-module convention, not to a modern right ideal
  (10238–10242).
- Rest groups are quotient left modules (10244–10268). Source gcd `(M,N)` is
  lattice supremum, lcm `[M,N]` is infimum, and coprimality means supremum top
  (10274–10280).
- “Primmodul” means a maximal one-sided submodule, equivalently a simple
  quotient, not a modern prime ideal (10584). “Fully reducible” means a finite
  direct sum of simple quotient modules (10588).
- “Same kind” is the explicit right-multiplication/intertwining relation at
  10630–10640. Theorem VI identifies it with quotient-module isomorphism.
- Finite rest-group order means finite `P`-vector-space dimension (10912).

## Explicit results

| Result | Source | Modern coverage |
|---|---|---|
| Satz I: `M = N ∩ L` and `N + L = ⊤` iff the quotient decomposes into two specified factors | 10329 | quotient/direct-product infrastructure is exact; arbitrary one-sided full iff needs packaging |
| Satz II: finite totally coprime intersection iff finite quotient decomposition | 10451; total coprimality 10441 | finite commutative ideal CRT is exact; generic noncommutative module formulation needs packaging |
| Satz III: every polynomial system has a finite module basis | 10502; hypotheses 10457–10462 | modern abstraction is `IsNoetherian`; Noetherianity of this skew operator ring is a high-value gap |
| Zusatz: the same finite-basis statement for quotient classes | 10506–10507 | finite-generation/quotient infrastructure exists once Noetherianity is supplied |
| Satz IV: finite decomposition into indecomposable quotient factors | 10513 | `GAP_CANDIDATE`; no direct module Krull–Schmidt/indecomposable API found |
| Satz V: two finite simple decompositions have mutually isomorphic matched factors, with extra identity/duplication clauses | 10620–10624 | matching core is a modern Mathlib form; source presentation needs packaging |
| Satz VI: same-kind modules iff their quotients are isomorphic | 10630–10644 | `GAP_CANDIDATE`; quotient lifts and right-multiplication maps are available |
| Satz VII: Satz V translated to totally coprime prime-module decompositions | 10681 | modern form after Satz VI; source dictionary remains to formalize |
| Satz VIII: a finite decomposition into mutually isomorphic factors has infinitely many decompositions over infinitely many central constants | 10690–10710 | `GAP_CANDIDATE`; proof requires at least two factors |
| Satz IX: criterion for infinitely many prime decompositions of a fully reducible module | 10882–10886 | `GAP_CANDIDATE`; semisimple/isotypic infrastructure is only a scaffold |
| Hilfssatz: an additional distinct prime divisor forces two listed factors to be same-kind | 10890–10892 | near `MATHLIB_MODERN_FORM` after translating the source dictionary |
| Satz X: criterion for infinitely many prime divisors of an arbitrary module | 10906 | `GAP_CANDIDATE` |
| Satz XI: quotient order equals the number of independent analytic solutions, with converse | 10918–10921 | `DEFERRED_INFRASTRUCTURE`; needs skew differential operators and analytic PDE hypotheses |
| Satz XII: same-kind differential modules transport complete solution systems by mutually inverse differential operators | 10970–10979 | algebraic kernel transport can be packaged; analytic solution semantics are deferred |

An unnumbered result at 10557–10567 gives actual uniqueness when the
cross-idempotent products form a diagonal scheme; commutation is sufficient.

## Exact Mathlib anchors

The audit against pinned Mathlib `v4.31.0` identified:

- `Submodule.ker_mkQ`, `LinearMap.ker_prod`, `LinearMap.range_prod_eq`,
  `LinearMap.quotKerEquivOfSurjective`, and `Submodule.quotEquivOfEq` for the
  noncommutative quotient-product map;
- `Submodule.prodEquivOfIsCompl` and `Submodule.quotientEquivOfIsCompl` for
  complementary submodules;
- `Ideal.quotientInfEquivQuotientProd` and
  `Ideal.quotientInfRingEquivPiQuotient` for commutative ideal CRT forms;
- `IsNoetherian`, `Submodule.FG`, and quotient Noetherian instances for the
  modern finite-basis abstraction;
- `IsSimpleModule`, `IsSemisimpleModule`,
  `Submodule.linearEquiv_of_sSup_eq_top`, and
  `Submodule.linearEquiv_of_le_sSup` for simple-factor matching; and
- `LinearMap.bijective_or_eq_zero` and isotypic-component infrastructure for
  later semisimple arguments.

No Ore-extension, skew-polynomial, skew-PBW, Weyl-algebra, packaged module
Krull–Schmidt, or analytic PDE implementation was found in the bounded
relevant subtrees. These are bounded absence findings, not repository-wide
proofs of absence.

## First promoted declaration

The smallest honest target is the forward algebraic heart of Satz I:

```lean
noncomputable def quotientInfEquivProdOfSupEqTop
    {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    (I J : Submodule R M) (h : I ⊔ J = ⊤) :
    (M ⧸ (I ⊓ J)) ≃ₗ[R] (M ⧸ I) × (M ⧸ J)
```

The promoted proof constructs `I.mkQ.prod J.mkQ`, computes its kernel, proves
surjectivity with `LinearMap.range_prod_eq`, and applies the first isomorphism
theorem. It is more general than the source's cyclic regular module but covers
only one direction and not the source's custom subgroup identifications.

The canonical file is
`MathematicalCommons/NoetherSchmeidler/NoncommutativeModules1920.lean` and is
imported by the Noether umbrella with explicit joint attribution. The bounded
Lean 4.31 check exited zero at 1,082,052,608 bytes, with empty stderr and
unchanged source. `#print axioms` reports exactly `propext`,
`Classical.choice`, and `Quot.sound`; receipt
`artifacts/build/NoncommutativeModules1920-20260825T0138493146531-a76d0ce8.receipt.json`.

## Source QA and scope cautions

Four likely transcription conflicts were reported to the German canon owner:

- line 11139 has an inconsistent extra `η` in `ξ-(y/x)η=ξ-a`;
- line 11141 says powers of `y`, while line 11205 and the dimension argument
  require powers of `η`;
- line 10586 points to §12.2 although the target example begins in §12.3; and
- line 11194 likely lost an exponential wrapper around the displayed common
  solution.

Three further formalization cautions were reported without treating them as
transcription corrections: Satz VIII's proof requires `α ≥ 2`; lines
10437–10440 divide by `k−1` despite the arbitrary-field setup; and Satz XI's
analytic hypotheses appear after its displayed statement. See
[`noether-canon-qa.tsv`](../../metadata/noether-canon-qa.tsv). No controlled
German text was changed.
