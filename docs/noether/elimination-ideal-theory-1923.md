# Noether 1923: elimination theory and general ideal theory

## Provenance and interpretation

- Work: P24, *Eliminationstheorie und allgemeine Idealtheorie* (1923).
- Controlled source: lines 13658–14145 of witness
  `NOETH-DE-AUTH-v052-20260815` / `ED0014_R785`.
- Witness SHA-256:
  `EE226847656BC4D65EDDA9E9BF9BB1D25797C0C6D672D267D94A97FD88C7AD58`.
- Baseline: Lean 4.31.0; Mathlib `v4.31.0`, commit
  `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`.

Let `k` be a field and `A = k[x₁,…,xₙ]`; Noether then makes a generic
linear coordinate change over `K = k(u_{μν})`. Her “Norm” is a successive
elimination/resultant form assembled through elementary divisors. It is not
Mathlib's `Algebra.norm`. Ideal divisibility is reverse inclusion. The source
also allows the unit ideal as “prime” and gives it dimension `−1`, unlike
`Ideal.IsPrime`; formal statements must isolate that endpoint convention.

## Source dictionary

| Lines | Source object | Modern model and status |
|---|---|---|
| 13683–13697 | polynomial rings, generic transformed ideals | `MvPolynomial`, scalar extension, `Ideal.map`/`comap`, generic linear `AlgEquiv`; primary preservation under pure-transcendental extension still needs packaging |
| 13701–13705 | ground ideal `gᵢ₋₁` | contraction after localization away from nonzero polynomials in the remaining variables |
| 13707–13731 | module presentation, elementary divisors, individual and total norms | Smith-normal-form and determinant substrate exists; Noether's successive elimination forms do not |
| 13733–13745 | primary factors, components, highest dimension, zeros | depends on elimination norms and primary decomposition |
| 13747–13760 | chain condition, prime/primary ideals, isolated components | Noetherian and primary vocabulary exists; pinned Mathlib lacks the required primary-decomposition package |
| 13762–13764 | perfect fields, separable part, reduced degree, exponent | `PerfectField`, separable/purely-inseparable closures and finite degree APIs provide modern vocabulary |

## Named results

| Result and source | Coverage | Exact boundary |
|---|---|---|
| Hilfssatz I, line 13770 | `GAP_CANDIDATE` | prime/primary preservation under generic linear change and pure-transcendental coefficient extension |
| Hilfssatz II, line 13784 | `GAP_CANDIDATE` | finite intersections commute with extension; irredundant primary decomposition also needs Hilfssatz I and decomposition infrastructure |
| Satz I, line 13790 | `GAP_CANDIDATE` | prime/primary elementary-divisor forms and norms are powers of one irreducible; dimension agrees with the radical |
| Satz II, line 13808 | `GAP_CANDIDATE` | prime iff every strict overideal has smaller Noether dimension; requires the elimination/dimension bridge |
| Hilfssatz III, line 13812 | `MATHLIB_EXACT` | a finite-dimensional domain over a field is a field (`FiniteDimensional.isUnit`, `fieldOfFiniteDimensional`) |
| Hilfssatz IV, line 13840 | `MATHLIB_EXACT` | a proper prime quotient is a domain and embeds in its fraction field |
| Satz III and corollary, lines 13852–13854 | mixed | generic-coordinate finiteness/trdeg is a gap; the algebraically closed zero-set corollary is modern Nullstellensatz coverage |
| Hilfssatz V, line 13866 | `GAP_CANDIDATE` | Frobenius-power property in every coordinate; perfect/Frobenius polynomial APIs are only substrate |
| Satz IV and corollary, lines 13878–13889 | `GAP_CANDIDATE` | identify the elementary-divisor form with a generic linear-form minimal polynomial and its inseparable-multiplicity factorization |
| Satz V, line 13903 | `GAP_CANDIDATE` | dimension equals quotient-field trdeg; arbitrary ideal dimension is maximum over associated primes |
| Satz VI, line 13909 | `GAP_CANDIDATE` | strict superprime of dimension one less; coheight order theory exists, generic-hyperplane/trdeg bridge does not |
| Satz VII, lines 13927–13931 | `MATHLIB_MODERN_FORM` | `Order.coheight`, prime series, and `ringKrullDim` supply the modern chain dimension, excluding Noether's top-ideal convention |
| Satz VIII, line 13939 | `GAP_CANDIDATE` | ground ideals are isolated components selected by associated-prime dimensions; norm factors count those dimensions |
| Hilfssatz VI, line 13943 | `NEW_PACKAGING` | local `groundIdeal_inf` promotes the binary localization-contraction core; finite families follow by iteration, while primary-component identification remains open |
| Satz IX, line 13991 | `GAP_CANDIDATE` | primary iff elementary-divisor form is a power of an irreducible |
| Satz X, line 14001 | `GAP_CANDIDATE` | associated primes correspond to largest primary norm factors and isolated components |
| Satz XI, lines 14029–14036 | `GAP_CANDIDATE` | conjugate-factor product and degree/multiplicity formula for each primary norm factor |
| Satz XII, line 14045 | `GAP_CANDIDATE` | irreducible elementary form is necessary for prime; irreducible norm is sufficient |
| Hilfssatz VII, line 14051 | `GAP_CANDIDATE` | inject the quotient by the elementary form into `A/I`; degree equals localized finrank |
| Satz XIII, line 14059 | `GAP_CANDIDATE` | over a perfect field, norm and elementary form coincide and irreducibility characterizes prime ideals |
| Satz XIV, line 14065 | `GAP_CANDIDATE` | `Nₚ = Eₚ^(p^g)` with `0 ≤ g ≤ (i−1)f`; pure-inseparable power-degree facts cover only a constituent |
| Hilfssatz VIII, line 14069 | `MATHLIB_MODERN_FORM` | above the separable part, every element degree is a `p`-power (`IsPurelyInseparable.finrank_eq_pow` and tower APIs) |
| Satz XV, line 14116 | `GAP_CANDIDATE` | absolute prime iff elementary form is absolutely irreducible; modern target is geometric integrality |
| Satz XVI, line 14122 | `GAP_CANDIDATE` | norm and elementary form specialize correctly outside finitely many number-field primes |
| Satz XVII, line 14134 | `GAP_CANDIDATE` | geometrically prime generic fiber remains geometrically prime for almost every arithmetic fiber |

The `MATHLIB_EXACT` labels cover modern constituents, not the paper's
elimination development. The major new infrastructure is the successive
Smith-normal-form elimination norm and its compatibility with primary
decomposition, specialization, and inseparability.

## Canon resolution and authorial caveats

- The `r_a` glyph conflict at line 14039 was accepted as `r_α` in ED0019 and
  is inherited by inactive successor ED0020. Existing ED0014 theorem records
  retain their original witness hash until an explicit rebase.
- Primary print confirms `Σ c_i(t) g_i(…)` at line 13871. The repeated `i` is
  historical dummy-index overloading and is preserved; Lean statements should
  use a fresh bound index without calling that a source correction.
- “Galoisscher Körper” at lines 13878–13895 should be modeled by a
  splitting/normal closure in the inseparable case, not blindly by modern
  `IsGalois`.
- “Absolute prime ideal” should become geometric integrality after arbitrary
  scalar extension.
- Sätze XVI–XVII require a fixed integral model and removal of denominator and
  leading-coefficient primes; coefficientwise reduction alone is too weak.

The canon owner also confirms that the unit-ideal/dimension `−1` convention is
printed. The controlled source was not edited by this repository.

## Formalization route

1. Extend the promoted binary `groundIdeal_inf` support lemma to the paper's
   finite-family presentation and connect the abstract localization to each
   polynomial elimination stage.
2. Add source-shaped wrappers for Hilfssatz III and the modern core of
   Hilfssatz VIII, without calling those new mathematics.
3. Define Noether's chain-dimension convention with an explicit top endpoint.
4. Build the first genuinely missing layer: the successive Smith-normal-form
   elimination form, carefully separated from univariate resultants and
   `Algebra.norm`.

The canonical support file is
`MathematicalCommons/Noether/EliminationIdealTheory1923.lean`. Its direct
bounded Lean 4.31 check exited zero with empty stderr, unchanged source, and a
1,155,006,464-byte peak. `#print axioms groundIdeal_inf` reports exactly
`propext`, `Classical.choice`, and `Quot.sound`; receipt
`artifacts/build/EliminationIdealTheory1923-20260825T0211115415031-5daeb94e.receipt.json`.
