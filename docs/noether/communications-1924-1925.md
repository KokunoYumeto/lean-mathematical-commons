# Noether 1924–1925 communications: ideal theory, Hilbert numbers, and characters

## Provenance and scope

- Controlled witness: `NOETH-DE-AUTH-v052-20260815` / `ED0014_R785`.
- Witness SHA-256:
  `EE226847656BC4D65EDDA9E9BF9BB1D25797C0C6D672D267D94A97FD88C7AD58`.
- Exact source packets: P26 lines 14206–14217, P27 lines 14219–14226,
  and P28 lines 14228–14241.
- Lean baseline: Lean 4.31.0 and Mathlib `v4.31.0`, commit
  `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`.

These are short research communications, not full papers. The audit separates
precise formal targets from historical summaries whose missing definitions or
hypotheses must be recovered from the later full papers. It does not silently
expand Noether's shorthand.

## P26: abstract characterization of ideal theory (1924)

The precise claim is the characterization at line 14214. In modern language,
for a commutative domain `R`, the two chain conditions are
`IsNoetherianRing R` and `IsArtinianRing (R ⧸ I)` for every nonzero ideal `I`;
the last condition is `IsIntegrallyClosed R`.

| Source item | Pinned Mathlib / local coverage | State |
|---|---|---|
| unit, no zero divisors, descending divisor chains terminate | domain plus `IsNoetherianRing` | `MATHLIB_MODERN_FORM` |
| ascending multiple chains terminate modulo every nonzero ideal | local `artinian_nonzero_quotients_iff_dimensionLEOne` | `NEW_PACKAGING` |
| add integral closure to characterize Dedekind ideal theory | `IsDedekindDomain`, `isDedekindDomain_iff` | local `isDedekindDomain_iff_integrallyClosed_and_artinianQuotients`; promoted `NEW_PACKAGING` |
| omit integral closure to obtain results for finite orders | no individual result or assumptions are stated in the notice | `BLOCKED_SOURCE` |

The phrase “completely equivalent to the ideal theory” is broader than the
listed ring axioms because the communication does not define the entire package
of factorization consequences. Only the ring characterization is a precise
formal target here.

The characterization is promoted in
`MathematicalCommons/Noether/AbstractIdealTheory1924.lean`. Its bounded Lean
4.31 module build exited zero with empty stderr, unchanged source, and a
1,369,149,440-byte peak. `#print axioms` reports exactly `propext`,
`Classical.choice`, and `Quot.sound`; receipt
`artifacts/build/MathematicalCommons-Noether-AbstractIdealTheory1924-20260825T0152132754901-698ede81.module.receipt.json`.

## P27: Hilbert numbers in ideal theory (1925)

All substantive text is line 14225.

| Source item | Pinned coverage | State / boundary |
|---|---|---|
| Hilbert numbers count residue classes of ideals | no grading, filtration, or coefficient field is fixed | `BLOCKED_SOURCE` as a definition |
| Hilbert's characteristic function eventually counts independent residue classes for polynomial ideals | `Polynomial.hilbertPoly` and its eventual-coefficient theorems are ingredients | `GAP_CANDIDATE`; the quotient-ideal/module theorem is not packaged |
| Macaulay generating function and Ostrowski evaluation in lower degree | neither formula is printed | `BLOCKED_SOURCE` |
| it suffices to define Macaulay's abstract numbers for a primary ideal `q` | `Ideal.IsPrimary` and radical/associated-prime vocabulary exist | `GAP_CANDIDATE`; primary decomposition is still missing |
| count independent classes over the residue field of the associated prime `p` | residue fields and localization exist | `BLOCKED_SOURCE` until localization versus maximality is fixed |
| successive systems are measured by composition lengths between ideal-quotient layers | `Submodule.colon`, `Module.length`, composition series, and Jordan–Hölder are ingredients | `GAP_CANDIDATE`; the length layer is close to `NEW_PACKAGING` |
| the resulting data replace the false general expression `q = p^n` for finite orders | comparative conclusion, not a quantified theorem | `BLOCKED_SOURCE` |

The controlled text writes `q/p`, `q/p²`, … . The mathematics requires the
increasing ideal-quotient (colon) chain `(q:p)`, `(q:p²)`, …; an ordinary module
quotient is generally undefined and points in the wrong direction. This may be
historical slash notation rather than a transcription error. Primary-witness
review now confirms exactly that reading: Lean uses colon ideals explicitly,
while source quotations preserve the printed slash.

## P28: group characters and ideal theory (1925)

| Source item | Modern assumptions and pinned coverage | State |
|---|---|---|
| finite-group representation theory as ideal theory of a semisimple group algebra | finite `G`, field `k`, and invertibility of `|G|`; Maschke and `IsSemisimpleRepresentation` | `MATHLIB_MODERN_FORM` |
| additive decomposition into directly indecomposable simple one-sided ideals, unique up to isomorphism | semisimple-module decomposition plus Jordan–Hölder | `MATHLIB_MODERN_FORM`; exact sentence unbundled |
| one-sided indecomposables in one two-sided block are mutually isomorphic | isotypic components of the regular module | `MATHLIB_MODERN_FORM` |
| isomorphism classes of one-sided indecomposables correspond to indecomposable two-sided ideals | `OrderIso.setIsotypicComponents` and fully invariant submodules | `NEW_PACKAGING` |
| indecomposable ideal classes correspond to irreducible representations | group-algebra/module equivalence and `irreducible_iff_isSimpleModule_asModule` | `MATHLIB_MODERN_FORM` |
| indecomposable two-sided ideals correspond to characters | valid for irreducible characters over a splitting field | `GAP_CANDIDATE` / `NEW_PACKAGING` |
| number of additive indecomposable summands equals the “rank” of the indecomposable ideals | split matrix-block decomposition is relevant, but “Rang” is undefined here | `BLOCKED_SOURCE` pending the full paper |

The bare word “Charaktere” at line 14238 must be read as irreducible
characters, with splitting-field and characteristic assumptions. Primary-
witness review confirms that bare `Charaktere` is genuinely printed; it is
retained with modern statement-scope apparatus rather than expanded in German.

## Next formalization targets

1. Define the localized colon-ideal layers for P27 and prove their elementary
   annihilation/residue-field structure before attempting the missing index-of-
   reducibility theorem.
2. Package the P28 bijection between isotypic classes of the regular module and
   fully invariant/two-sided blocks under explicit semisimplicity assumptions.
