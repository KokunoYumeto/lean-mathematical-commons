# Noether 1924: elimination theory and ideal theory

## Provenance and scope

- Work: P25, *Eliminationstheorie und Idealtheorie* (1924).
- Controlled source: lines 14147–14204 of witness
  `NOETH-DE-AUTH-v052-20260815` / `ED0014_R785`.
- Witness SHA-256:
  `EE226847656BC4D65EDDA9E9BF9BB1D25797C0C6D672D267D94A97FD88C7AD58`.
- Baseline: Lean 4.31.0; Mathlib `v4.31.0`, commit
  `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`.

This four-page conference report compresses the univariate theory into four
steps and then proposes parallel multivariate steps: primary decomposition,
generic-zero fields, factorization of a successive elimination norm, and
multiplicity. The report is mathematically dense but does not define enough of
the multistage norm construction to reconstruct it safely in Lean. Mathlib's
`Algebra.norm` and univariate `Polynomial.resultant` must not be substituted for
Noether's elementary-divisor norm.

Historical ideal divisibility reverses Lean's inclusion order. The “least
common multiple” of ideals is intersection (`inf`), and the source's
“Galoisscher Körper” is best read as a splitting field unless separability is
made explicit.

## Claim-level coverage

| ID | Lines | Source claim | Pinned Mathlib coverage | Classification |
|---|---:|---|---|---|
| 01 | 14162 | coefficient domain is a field; “Primfunktion” means irreducible | `Field`; `Irreducible` | `MATHLIB_EXACT` |
| 02 | 14164–14168 | factorization into powers of distinct irreducibles | polynomial UFD instances and prime-factor existence | `MATHLIB_MODERN_FORM` |
| 03 | 14168 | zeros of the product are the union of zeros of the prime factors | evaluation preserves products and powers | `NEW_PACKAGING` |
| 04 | 14170 | construct a root field as the quotient by an irreducible polynomial | `AdjoinRoot`, `AdjoinRoot.instField` | `MATHLIB_EXACT` |
| 05 | 14170 | every root-generated field has the same abstract quotient model | `AdjoinRoot.equiv`; minpoly/adjoin equivalences | `MATHLIB_MODERN_FORM` |
| 06 | 14172 | existence, generation, and uniqueness of a splitting field | `Polynomial.SplittingField`; `Polynomial.IsSplittingField.algEquiv` | `MATHLIB_EXACT` |
| 07 | 14174 | degree equals the dimension of residue classes modulo a polynomial | `finrank_quotient_span_eq_natDegree` | `MATHLIB_EXACT` |
| 08 | 14174 | over an algebraically closed field this becomes root multiplicity | root-count and multiplicity APIs | `MATHLIB_MODERN_FORM` |
| 09 | 14176 | ideal definition | `Ideal` | `MATHLIB_EXACT` |
| 10 | 14176 | a zero of an ideal annihilates every member | `MvPolynomial.zeroLocus`; `mem_zeroLocus_iff` | `MATHLIB_EXACT` |
| 11 | 14176 | every ideal in finitely many polynomial variables has a finite basis | `MvPolynomial.isNoetherianRing` and Noetherian finite generation | `MATHLIB_EXACT` |
| 12 | 14176 | zero set of a generating family equals the zero set of its span | `MvPolynomial.zeroLocus_span`; `Ideal.span` | `MATHLIB_EXACT` |
| 13 | 14176 | every univariate polynomial ideal is principal, uniquely up to a unit | Euclidean/PID instances; equality of principal spans | `MATHLIB_MODERN_FORM` |
| 14 | 14180 | definitions of prime and primary ideals | `Ideal.IsPrime`; `Ideal.IsPrimary` | `MATHLIB_EXACT` |
| 15 | 14180 | a primary ideal has prime radical and contains a power of it | `Ideal.isPrime_radical`; `exists_radical_pow_le_of_fg` | `MATHLIB_MODERN_FORM` |
| 16 | 14180–14185 | irredundant finite primary decomposition | no pinned end-to-end theorem found | `GAP_CANDIDATE` |
| 17 | 14185 | uniqueness of the associated prime ideals | no pinned associated-prime uniqueness package found | `GAP_CANDIDATE` |
| 18 | 14182–14185 | product of radical powers lies in the ideal and zero loci form a union | conditional radical/zero-locus ingredients only | mixed packaging/gap |
| 19 | 14187 | quotient by a proper prime ideal is a nontrivial domain | `Ideal.Quotient.nontrivial_iff`; `isDomain_iff_prime` | `MATHLIB_EXACT` |
| 20 | 14187 | its fraction field exists and is unique up to isomorphism | `FractionRing`; `IsFractionRing.algEquiv` | `MATHLIB_EXACT` |
| 21 | 14187 | coordinate images form a generic zero, have relation ideal exactly the prime, and generate the fraction field over `P` | quotient, fraction-ring, `aeval`, and `IntermediateField.adjoin` APIs | promoted `NEW_PACKAGING` |
| 22 | 14187 | a transcendence basis has size `k`; every `k+1` elements are dependent; the printed text says `k<n` | `Algebra.trdeg`; transcendence-basis and cardinal-range APIs | valid `k≤n` bound and strict form under `I≠0` promoted; unqualified print remains apparatus |
| 23 | 14189 | after generic coordinates, the function field is finite algebraic over a rational-function field | Noether normalization APIs | `MATHLIB_MODERN_FORM` |
| 24 | 14189 | split the fundamental polynomial into linear factors | splitting-field APIs are exact; identification of the fundamental polynomial is missing | exact core / gap bridge |
| 25 | 14189 | the fundamental polynomial is the product over all zeros | product-over-roots exists; generic-projection bridge is missing | `GAP_CANDIDATE` |
| 26 | 14189 | define `N(p)` from the nonunit elementary divisors of a module presentation | module, presentation, normalization, and independence are under-specified | `BLOCKED_SOURCE` / deferred |
| 27 | 14191 | only finitely many elementary divisors at each stage are nonunits | exact finite presentation is not supplied | `BLOCKED_SOURCE` |
| 28 | 14191–14195 | total norm factors correspond to associated primes | depends on the missing norm and primary decomposition | `BLOCKED_SOURCE` |
| 29 | 14195 | multiplicity is a degree/residue dimension of isolated “Grundideal” layers | the layers are not defined in this report | `BLOCKED_SOURCE` |
| 30 | 14197 | the univariate theory is recovered from the ideal theory | UFD/root-field pieces exist; norm identification is blocked | mixed packaging/blocked |
| 31 | 14199 | the ideal norm has resultant meaning | univariate resultants exist; the multistage identification does not | `BLOCKED_SOURCE` / gap |

The chief pinned-Mathlib gap exposed by the report is Noetherian primary
decomposition together with uniqueness of associated primes. Item 21 is now
promoted: the coordinate images in the fraction field of the prime quotient
form a generic zero, and a polynomial evaluates to zero there exactly when it
belongs to the prime ideal. The same module now proves that adjoining the range
of this coordinate tuple as an intermediate field gives the whole fraction
field, formalizing `R = P(α₁, ..., αₙ)`. From that field-generation theorem it
also proves that the transcendence degree is bounded by the cardinality of the
actual generic-coordinate range and, for `Fin n`, by `n`. This is the safe
non-strict theorem forced by the allowed zero prime; it does not rewrite the
printed strict statement. A second theorem proves the strict bound when the
prime ideal is explicitly nonzero: equality would make the full generic tuple
a transcendence basis, contradicting any nonzero relation from the ideal.

The canonical module
`MathematicalCommons/Noether/EliminationIdealTheorySurvey1924.lean` has the
arbitrary-index field-generation theorem and arbitrary-index/finite-`Fin n`
vanishing-kernel forms, together with arbitrary-index and finite-coordinate
transcendence-degree bounds, including the strict nonzero-prime form. Its direct
Lean 4.31 check exited zero with empty stderr, unchanged source, and a
1,396,658,176-byte observed peak under the 4.5 GiB watcher. All seven
declarations report exactly `propext`,
`Classical.choice`, and `Quot.sound`; receipt
`artifacts/build/EliminationIdealTheorySurvey1924-20260825T1455476550253-56fa99cb.receipt.json`.

## Canon and statement-scope review

- Primary print confirms `0 ≤ k < n` at line 14187. Because the zero prime is
  allowed and has transcendence degree `n`, a safe modern theorem must use
  `k ≤ n` or assume the prime is nonzero. The German is retained with critical
  apparatus because those are distinct repairs.
- Primary print also confirms `Galoisscher/Galoisschen Körper` at lines 14172
  and 14189. It is historical splitting/normal-field terminology; Lean uses
  `Polynomial.IsSplittingField` generally and `IsGalois` only with separability.
- Line 14170 reuses `R` for the constructed field and the parenthesized residue
  field. That may be intentional historical typography and is review-only.

No German word is missing at those loci. The controlled source was not edited;
the append-only primary-witness decisions are recorded in the canon reference
packet, while ED0020 remains inactive.

## Formalization route

1. Package the univariate zero-set union and residue-dimension statements.
2. Develop a reusable Noetherian primary-decomposition layer rather than
   assuming the missing theorem under a historical name.
3. Recover the exact module presentations from the full 1923 paper and
   Hentzelt material before defining the successive norm.
