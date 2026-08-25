# Noether 1919: integral invariants of binary forms

This note maps Emmy Noether's *Die Endlichkeit des Systems der ganzzahligen
Invarianten binärer Formen* to pinned Mathlib and records the first staged
support declaration. The paper combines finite generation over the integers,
determinantal invariants, multisymmetric polynomials, straightening, and an
integral presentation of the Plücker relation ideal.

## Controlled source and conventions

- Work ID: **P15**; packet lines 9284–9901.
- Controlled witness: `NOETH-DE-ED-0014`, SHA-256
  `EE226847656BC4D65EDDA9E9BF9BB1D25797C0C6D672D267D94A97FD88C7AD58`.
- Authority status: immutable formalization witness, not a claim that this is
  the final critical German text.

No source text was changed during the audit. The main theorem at lines
9303–9305 concerns integral relative invariants of binary forms, first one
form and then finite systems. The coefficient convention matters: line 9397
warns that the coefficients are used directly rather than with the customary
binomial factors. A formal polynomial action must preserve that convention.

## Result inventory

| Result | Source | Mathlib boundary |
|---|---|---|
| Finite generation of the integer algebra of integral relative invariants of binary forms | 9303–9305; one form 9513; systems 9515 | `GAP_CANDIDATE` |
| Satz I: every integral invariant of binary linear forms is an integral polynomial in the brackets `(ik)` | 9320; proof completed 9836 | `GAP_CANDIDATE` |
| Satz II: a quotient-closed system of nonnegative monomials has a finite multiplicative basis | 9322–9330 | `MATHLIB_MODERN_FORM` for the multiplicatively closed application through `Submonoid.fg_of_divisive`; literal source generality needs review |
| Satz III: row-symmetric integral polynomials have a finite basis, with polarized power sums and elementary functions | 9332–9349 | `GAP_CANDIDATE`; ordinary symmetry exists, multisymmetric row symmetry does not |
| Explicit bounded-exponent orbit-sum basis | 9350–9361 | `GAP_CANDIDATE` |
| Satz IV: finite generation of integral polynomials among `G(F₁,…,Fₖ)/a` | 9363–9379 | small `GAP_CANDIDATE` from Noetherian ideal-preimage infrastructure |
| Algebraic independence transfers relations from factored forms to generic coefficients | 9411–9424 | `MATHLIB_MODERN_FORM`; homogenization wrapper missing |
| Correspondence between binary-form invariants and row-symmetric equal-multihomogeneous polynomials in linear factors | 9427–9458 | `GAP_CANDIDATE` |
| Every mod-`p` bracket relation lifts integrally, `Mₚ = (M,p)` | 9534–9571 | `GAP_CANDIDATE` |
| Quadratic Plücker relations generate the full relation ideal integrally and after every prime reduction | 9573–9594; 9830–9836 | high-value `GAP_CANDIDATE` |
| Standard-monomial straightening and uniqueness | 9637–9645; 9695–9795 | `GAP_CANDIDATE`; source formulas currently have open canon QA |
| Finite-group orbit averaging | 9851–9856 | `MATHLIB_EXACT` after modeling the representation |
| Finite generation for finite linear groups with algebraic-integer matrix entries | 9858–9890 | abstract core is the local green 1926 fixed-ring theorem; polynomial/number-ring specialization remains a `GAP_CANDIDATE` |
| Rational-integer generators under closure by algebraic conjugation | 9892–9896 | `GAP_CANDIDATE` |

Historical results cited from Mertens, Hilbert, Gordan, Ostrowski, Clebsch, and
Schur are dependencies or comparisons, not separate Noether-result records.

## Exact pinned Mathlib anchors

The audit used Mathlib `v4.31.0` at resolved revision
`fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`.

- `Submonoid.fg_of_divisive` and `AddSubmonoid.fg_of_subtractive` give the
  modern Dickson-lemma-style finite-generation core of Satz II when the
  exponent set is multiplicatively/additively closed.
- `AddSubmonoid.fg_eqLocusM` covers the nonnegative integral solutions of the
  linear Diophantine equations used in the application.
- `MvPolynomial.esymmAlgEquiv` and
  `MvPolynomial.esymmAlgHom_injective` cover ordinary symmetric polynomials,
  not Noether's simultaneous permutation of rows with several columns.
- `MvPolynomial.isNoetherianRing` and `Ideal.fg_of_isNoetherianRing` are the
  main ingredients for Satz IV's ideal-preimage proof.
- `GroupAlgebra.average`, `Representation.averageMap_invariant`, and
  `Representation.averageMap_id` cover the finite-group averaging step.
- `Algebra.IsInvariant.isIntegral`, `fg_of_fg_of_fg`, and the promoted local
  `fixedPoints_finiteType` theorem cover the abstract finite-type heart of the
  last finite-group application.

Pinned `Module.Grassmannian` does not provide the coordinate-ring Plücker
presentation needed for Satz I or for equality of the quadratic and full
relation ideals. This is a bounded relevant-source absence finding, not a
repository-wide proof of absence.

## Promoted support declaration

The file
`MathematicalCommons/Noether/IntegralInvariants1919.lean` defines

```lean
def bracket (α β : ι → R) (i k : ι) : R :=
  α i * β k - β i * α k
```

and proves `pluckerRelation`, the elementary identity

```text
[ik][rs] - [ir][ks] + [is][kr] = 0.
```

This is exactly the smallest algebraic support fact at lines 9573–9581. It
does **not** prove that these quadrics generate the relation ideal, give a
normal form, lift relations modulo primes, or prove Satz I. The declaration is
green against pinned Mathlib v4.31.0 under a one-thread 5 GiB watcher. Receipt
`artifacts/build/IntegralInvariants1919-20260825T0029213983058-a9f740c7.receipt.json`
binds the source and environment; `#print axioms` reports only `propext` and
`Quot.sound`.

## Open canon QA

The following were reported to the German canon owner on 2026-08-24:

- line 9653 gives `ξ₁₄ = ξ₁₃` for the row-4/row-3 specialization but
  appears also to require `ξ₂₄ = ξ₂₃`, as confirmed by the general
  substitutions at line 9799;
- lines 9699 and 9703 repeat the same monomial although the prose treats two
  complementary normalized cases; the exact repaired second display needs
  scan verification; and
- line 9882 has `wᵢ = ωᵢ/h`, while line 9886 reverses it to
  `ωᵢ = wᵢ/h`; the latter does not yield formula (4).

Two review-only points were also sent without asserting defects: line 9841
dates P07 to 1915 although its heading and bibliography give 1916, and line
9821 reverses the usual bracket orientation. No formal statement may silently
choose a repaired reading while these remain open.

## Development order

After the elementary Plücker identity is built, the most useful sequence is:

1. formalize the bracket polynomial map and the quadratic relation ideal;
2. define crossing-free standard monomials and prove one straightening step;
3. prove existence and uniqueness of normal forms after canon reconciliation;
4. identify the full integral kernel and its reduction modulo primes;
5. deduce Satz I and transport through the factored-form correspondence; and
6. combine multisymmetric finite generation, Satz IV, and the fixed-ring
   theorem to reach the main integral-invariant finite-generation result.

This keeps the trivial identity, the Plücker presentation, and the headline
finite-generation theorem as three distinct coverage levels.
