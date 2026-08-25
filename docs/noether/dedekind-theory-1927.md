# Noether 1927: abstract Dedekind ideal theory

This note maps Emmy Noether's *Abstrakter Aufbau der Idealtheorie in
algebraischen Zahl- und Funktionenkörpern* to pinned Mathlib. The paper gives
an axiom system for the rings now modeled as Dedekind domains, develops unique
prime-power ideal factorization from those axioms, proves a converse, and ends
with the finite-length and Jordan–Hölder theory of modules.

## Controlled source

- Work ID: **P30**; packet lines 14344–15596.
- Controlled witness: `NOETH-DE-ED-0014`, SHA-256
  `EE226847656BC4D65EDDA9E9BF9BB1D25797C0C6D672D267D94A97FD88C7AD58`.
- Authority status: immutable formalization witness, not a claim that this is
  the final critical German text.

No source text was changed during this audit. At lines 14391–14404 Noether
explicitly corrects a gap in her 1921 proof: it had used a multiplicative unit
without assuming one. That is an authorial mathematical correction, credited
in the source to a warning from P. Urysohn and repairs by E. Artin and W. Krull;
it is not a transcription discrepancy.

## The five axioms

The introduction at lines 14354–14389 states that unique prime-power ideal
factorization is equivalent to the following conditions on a commutative ring:

1. the ascending chain condition on ideals;
2. the descending chain condition on ideals modulo every nonzero ideal;
3. a multiplicative identity;
4. no zero divisors; and
5. integral closure in the fraction field.

In modern Lean, Axiom I is `IsNoetherianRing`; Axioms III and IV are structural
ring/domain assumptions; and Axiom V is the integral-closure clause in
`isDedekindDomain_iff`. Axiom II is naturally expressed as

```lean
∀ I : Ideal R, I ≠ ⊥ → IsArtinianRing (R ⨸ I)
```

because ideals of the quotient correspond to ideals of `R` containing `I`.
Mathlib's modern Dedekind characterization uses `Ring.DimensionLEOne R`
instead. The source-shaped equivalence between these two presentations, under
the appropriate Noetherian/domain assumptions, was not found as a declaration
in the bounded pinned-source audit.

## Source result inventory

| Result | Source | Mathlib boundary |
|---|---|---|
| Five-axiom characterization of rings with unique prime-power ideal factorization | 14354–14389 | `MATHLIB_MODERN_FORM` via `IsDedekindDomain` and `isDedekindDomain_iff`; the Axiom-II bridge remains open |
| Equivalent definitions of an integral element and the finite-order Hilfssatz | 14589–14635 | `MATHLIB_MODERN_FORM` via `IsIntegral` and `Algebra.IsIntegral.of_finite` |
| Transitivity of integral dependence | 14666–14678 | `MATHLIB_EXACT` through `isIntegral_trans` and integral algebra towers |
| Dedekind corollary I: a last integral term in `c, cβ, cβ², ...` | 14693–14715 | source-shaped `GAP_CANDIDATE` |
| Dedekind corollary II: `β = m/n` with `m²/n` still nonintegral | 14726–14740 | high-value source-shaped `GAP_CANDIDATE` |
| Modulsatz: finite modules inherit ascending or descending chain conditions | 14772–14830 | `MATHLIB_MODERN_FORM` via `Module.Finite`, `IsNoetherian`, and `IsArtinian` transfer |
| Integral closure in a finite first-kind/separable extension preserves the axioms | 14875–14895 | `MATHLIB_MODERN_FORM` via `IsIntegralClosure.isDedekindDomain` |
| First and second module/ring isomorphism theorems and direct-sum/CRT consequences | 14913–14950 | `MATHLIB_EXACT` in quotient/isomorphism infrastructure and `Ideal.quotientInfRingEquivPiQuotient` |
| Satz I: finite irreducible decomposition under Axiom I | 15004 | `MATHLIB_MODERN_FORM` via `exists_infIrred_decomposition` |
| Satz II: irreducible ideals are primary | 15011 | `MATHLIB_EXACT` via `InfIrred.isPrimary` |
| Satz III: primary decomposition with distinct associated primes | 15034 | `MATHLIB_MODERN_FORM` via `Submodule.isLasker` and minimal-primary-decomposition APIs |
| An Artinian domain is a field | 15046 | `MATHLIB_EXACT` via `IsArtinianRing.isField_of_isDomain` |
| Satz IV: uniqueness of the nonunit primary components under the double-chain hypothesis | 15065 | `MATHLIB_MODERN_FORM`; source packaging remains open |
| Satz V: unique product of pairwise coprime primary ideals | 15081 | ingredients exist, but the source-shaped result remains a `GAP_CANDIDATE` |
| Cancellation and identification of primary ideals as prime powers | 15108–15231 | modern Dedekind ideal divisibility/factorization supplies the result after translation |
| Satz VI: unique prime-power factorization of nonzero ideals | 15233 | `MATHLIB_MODERN_FORM` via `Ideal.uniqueFactorizationMonoid` and explicit height-one factorization |
| Converse from unique prime-power factorization to the five axioms | 15243–15369 | component results exist; the complete source-direction package is a `GAP_CANDIDATE` |
| Nonzero fractional ideals form an abelian group | 15318–15341 | `MATHLIB_EXACT`, strengthened by the `FractionalIdeal` semifield instance |
| Double chain condition iff existence of a composition series | 15415–15438 | `MATHLIB_EXACT` via finite-length equivalences |
| Jordan–Hölder uniqueness of composition factors | 15438–15527 | `MATHLIB_EXACT` via `CompositionSeries.jordan_holder` and the submodule Jordan–Hölder lattice |

## Exact pinned Mathlib anchors

The audit used Mathlib `v4.31.0` at resolved revision
`fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`. The principal declarations are:

- `IsDedekindRing`, `IsDedekindDomain`, and `isDedekindDomain_iff`;
- `Ring.DimensionLEOne`;
- `Ideal.krullDimLE_zero_quotient_iff_forall_minimalPrimes_isMaximal`,
  `IsNoetherianRing.isArtinianRing_of_krullDimLE_zero`, and
  `isArtinianRing_iff_isNoetherianRing_krullDimLE_zero`;
- `IsIntegral`, `Algebra.IsIntegral.of_finite`, and `isIntegral_trans`;
- `IsIntegralClosure.finite` and `IsIntegralClosure.isDedekindDomain` for
  finite separable extensions;
- `IsNoetherian`, `IsArtinian`, `IsNoetherianRing.of_finite`, and
  `IsArtinianRing.of_finite` for finite-module transfer;
- `Ideal.quotientInfRingEquivPiQuotient` and
  `Ideal.quotientInfEquivQuotientProd` for CRT;
- `exists_infIrred_decomposition`, `InfIrred.isPrimary`,
  `Submodule.isLasker`, and minimal-primary-decomposition APIs;
- `Ideal.dvd_iff_le`, `Ideal.uniqueFactorizationMonoid`,
  `Ideal.finite_factors`, and
  `Ideal.finprod_heightOneSpectrum_factorization`;
- the `FractionalIdeal.semifield` instance;
- `exists_compositionSeries_of_isNoetherian_isArtinian`,
  `isFiniteLength_iff_isNoetherian_isArtinian`, and
  `isFiniteLength_iff_exists_compositionSeries`; and
- `JordanHolderModule.instJordanHolderLattice` and
  `CompositionSeries.jordan_holder`.

These are modern encodings, not necessarily source-identical statements. In
particular, unique factorization is expressed through a factorization monoid
or a finite product indexed by height-one primes, and Jordan–Hölder is stated
for composition series in a `JordanHolderLattice`.

## Promoted Axiom-II bridge

The smallest theorem that materially closes the historical/modern boundary is
the Axiom-II bridge now promoted in
`MathematicalCommons/Noether/DedekindTheory1927.lean`:

```lean
theorem artinian_nonzero_quotients_iff_dimensionLEOne
    [IsNoetherianRing R] :
    (∀ I : Ideal R, I ≠ ⊥ → IsArtinianRing (R ⧸ I)) ↔
      Ring.DimensionLEOne R
```

The forward direction sends a nonzero prime `P` to the Artinian domain
`R ⧸ P`, hence a field, proving maximality. The reverse direction uses
`Ideal.krullDimLE_zero_quotient_iff_forall_minimalPrimes_isMaximal` to make the
quotient zero-dimensional, then
`IsNoetherianRing.isArtinianRing_of_krullDimLE_zero`. No domain assumption is
needed. Receipt
`artifacts/build/DedekindTheory1927-20260825T0030012236532-128b5301.receipt.json`
records a clean one-thread build under a 5 GiB ceiling; `#print axioms` reports
`propext`, `Classical.choice`, and `Quot.sound` for all three declarations.

After that bridge, the next honest targets are Dedekind corollary II and a
source-shaped equivalence between the five axioms and unique prime-power ideal
factorization. The latter must not be advertised as absent mathematics merely
because Mathlib packages its directions differently.

## Build and infrastructure state

The exact pinned source packages were restored from revision-specific archives,
and only the targeted prebuilt cache closure was unpacked. No `lake update`,
Git operation, broad rebuild, or unbounded compilation was used. The promoted
module was checked directly with one Lean thread, a 5 GiB process-tree ceiling,
an exclusive build lock, source/environment hashing, and explicit
`#print axioms` output.
