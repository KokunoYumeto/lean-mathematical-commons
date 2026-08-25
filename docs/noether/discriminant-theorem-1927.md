# Noether 1927: the discriminant theorem for orders

This note maps Emmy Noether's *Der Diskriminantensatz für die Ordnungen
eines algebraischen Zahl- oder Funktionenkörpers* to pinned Mathlib. The
paper reduces divisibility of an order discriminant to the trace pairing on a
finite-dimensional residue algebra. It then characterizes the algebras with
nonzero discriminant as finite products of separable fields and globalizes the
criterion from a principal base ring to relative orders by localization.

The maximal-order ramification criterion has strong modern Mathlib coverage.
The source-shaped theorem for arbitrary finite orders, with proper primary
components and inseparable residue fields as the two obstructions, is not a
pinned declaration.

## Controlled source

- Work ID: **P31**.
- Title: *Der Diskriminantensatz für die Ordnungen eines algebraischen Zahl-
  oder Funktionenkörpers*.
- Publication heading: *Journal f. d. reine u. angew. Math.* 157 (1927),
  pp. 82–104; source lines 15600–15606.
- Controlled witness: `NOETH-DE-ED-0014`, packet lines 15600–16088.
- Controlled file:
  `C:\Users\Floris\Documents\interlanguage\03_projects\noether\07_german_canon_control\candidates\ED0014\noether.tex`.
- Witness SHA-256:
  `EE226847656BC4D65EDDA9E9BF9BB1D25797C0C6D672D267D94A97FD88C7AD58`.
- Authority status: immutable formalization witness, not a claim that this is
  the final critical German text.
- The closing date at line 16083 is 30 March 1926. Its difference from the
  1927 publication year is normal submission/publication chronology.

No controlled source text was changed during this audit. Mathlib was checked
at input revision `v4.31.0`, resolved revision
`fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`. At audit time the local dependency
cache was absent, so declaration checks used bounded named files from the
official Mathlib repository at that exact revision. The later targeted cache
recovery enabled promotion of the independent quotient-discriminant lemma only.

## Source dictionary and assumptions

The following translations are necessary before comparing statements.

- The footnote at line 15610 says that **order** always means a finite order
  and **ring** always means a commutative ring. This convention controls the
  apparently broader definition at line 16026.
- A finite-dimensional `P`-algebra is *vollständig reduzibel* when its zero
  ideal is a finite intersection/product of prime ideals, equivalently when it
  is a finite product of fields (15788). This is reduced Artinian, not merely
  semisimple as a module in an unrelated noncommutative sense.
- *Erster Art* and *zweiter Art* mean separable and inseparable finite residue
  field extension respectively (15780).
- Noether's additive *direkte Summe* of rings is the modern finite product of
  rings, with orthogonal idempotents.
- Her coefficient-field extension `R[\bar P]` is modern scalar extension
  `\bar P ⊗[P] R`. Lines 15642 and 15681 deliberately replace fields or
  algebras by equivalent disjoint copies; this is historical constructional
  language, not an extra modern hypothesis.
- In §8, *Quotientenring* means localization at elements coprime to the
  specified ideal, not an ideal quotient.
- Historical ideal divisibility reverses inclusion. The statement that a base
  prime is "divisible by the square" of an extension prime translates to
  `Ideal.map f p ≤ P ^ 2`.

The coefficient/action assumptions change by section:

1. **§§1–3:** `P` is a field and `R` a finite-dimensional commutative
   unital `P`-algebra; `\bar P` is an algebraic closure when specified.
2. **§§4–5:** `Σ` is a domain, `R` is a unital `Σ`-algebra, and every
   relevant `Σ`-submodule has a finite linearly independent basis. Two bases
   of the same module differ by a matrix whose determinant is a unit (15852).
3. **§6:** the base is again a field `P` and `R` is finite-dimensional.
4. **§7:** `H` is a principal ideal domain, `K = Frac(H)`, `L/K` is finite
   separable, `S` is the integral closure of `H` in `L`, and `T ⊆ S` is a
   finite order, normally of full rank `n = [L : K]` (16024–16030).
5. **§8:** `H` is a multiplication ring in Noether's sense: a domain with
   unique prime-power factorization of nonzero proper ideals and maximal
   nonzero primes (16057). The modern lane is `IsDedekindDomain`.

## Author-labelled results

| Source result | Exact lines and assumptions | Pinned Mathlib boundary | Coverage |
|---|---|---|---|
| §3.2 **Satz**: first-kind complete reducibility is preserved and reflected by extension to an algebraic closure | Statement 15792; proof 15794–15828; finite-dimensional commutative `P`-algebra | `Algebra.Etale.iff_exists_algEquiv_prod`; forward direction `Algebra.Etale.baseChange`; Artinian product decomposition `IsArtinianRing.equivPi` | `MATHLIB_MODERN_FORM` for the product/separability translation, with the reverse-descent axiom warning below |
| §3.3 **Folgerung**: over the algebraic closure the algebra splits into rank-one copies, already over a finite extension `Ω/P` | Statement 15830; proof 15832–15843 | `Algebra.FormallyEtale.equivPiOfIsSepClosed` gives the split product over a separably closed field | `MATHLIB_MODERN_FORM` for splitting over the closure; the single finite splitting field package is a `GAP_CANDIDATE` |
| §6.3 **Satz**: nonzero discriminant iff complete reducibility of first kind | Statement 15992; proof 15994; finite-dimensional commutative `P`-algebra | `Algebra.discr`, `Algebra.discr_not_zero_of_basis`, `Algebra.traceForm_nondegenerate_tfae`, and the étale product classification cover the field/product constituents | `GAP_CANDIDATE` for one general finite-algebra theorem |
| §7.3 **Diskriminantensatz** for finite orders over a PID | Statement 16045; proof 16049; hypotheses 16024–16032 | quotient trace, discriminant, primary-decomposition, separability, and localization APIs are constituents | `GAP_CANDIDATE`; no source-shaped arbitrary-order theorem |
| §8.5 **Allgemeiner Diskriminantensatz** for relative orders | Statement 16075; proof 16077; hypotheses 16055–16073 | `IsDedekindDomain`, localization, `differentIdeal`, `Ideal.relNorm`, and ramification-index APIs cover the maximal-order lane | `GAP_CANDIDATE`; arbitrary relative orders remain uncombined |

## Constituent result inventory

### Introduction and proof plan

| Source | Result | Mathlib coverage |
|---|---|---|
| 15608 | Dedekind maximal-order theorem: a rational prime divides the field discriminant iff some prime above it occurs with exponent at least two | `MATHLIB_MODERN_FORM`, derivable from `NumberField.not_dvd_discr_iff_forall_mem`, unramifiedness, and `Ideal.ramificationIdx_ne_one_iff` |
| 15610 | For every finite number-field order, `p` divides its discriminant iff `pT` has a proper primary component | `GAP_CANDIDATE` |
| 15612 | In the maximal order, primary ideals are prime powers, so the preceding statement specializes to Dedekind's theorem | `MATHLIB_MODERN_FORM` through Dedekind ideal factorization and ramification index |
| 15614 | Passing to `T/pT` turns the factorization of `pT` into the zero-ideal decomposition of a finite-dimensional residue algebra | quotient and ideal-map APIs are exact; source bridge is modern packaging |
| 15616 | Over a perfect coefficient field, complete reducibility is detected after algebraic-closure base change; over the closure it is equivalent to nonzero discriminant; the order discriminant reduces to the quotient discriminant | the three links have substantial pinned constituents, but the complete chain is not one declaration |
| 15618 | Over imperfect residue fields, a proper primary component **or** an inseparable residue-field prime is the obstruction | residue separability is exact; the order theorem is a `GAP_CANDIDATE` |
| 15620 | The relative-order theorem follows by localizing at every base prime | localization infrastructure exact; combined theorem absent |
| 15622–15624 | A module basis survives reduction modulo every base prime, while a primitive-element power basis may fail to do so | exact finite-free/quotient-basis infrastructure; this is a methodological warning, not a separate gap theorem |
| 15626 | Expected future ramification exponents should be expressible as composition-series lengths | authorial speculation only |

### §1: scalar extension and ideals

| Source | Result | Mathlib coverage |
|---|---|---|
| 15632–15636 | Generated ring, ideal, and module; adjoining elements | exact modern constructors `Subring.closure`, `Ideal.span`, `Submodule.span`, and `Algebra.adjoin` |
| 15638–15683 | Existence of `R[\bar P]`, preservation of linear independence, and extension of a basis | `Algebra.TensorProduct` and `Basis.baseChange` give the modern exact model |
| 15685 | The extended ideal consists of finite `\bar P`-linear combinations of elements of the original ideal | `Ideal.map` and submodule base change |
| 15687 | Every ideal contracts back from its scalar extension | faithfully-flat base-change injectivity (`Module.FaithfullyFlat.baseChange_inj`) supplies the modern core; the exact ideal map/comap presentation is not a dedicated declaration |
| 15689–15694 | Contraction of a prime is prime and the original quotient embeds into the extended quotient | `Ideal.comap_isPrime` and quotient-kernel/range equivalences |

### §2: finite-rank algebras and primary components

| Source | Result | Mathlib coverage |
|---|---|---|
| 15700–15702 | Common finite rank for bases; ascending and descending chains of subspaces and ideals terminate | finite-dimensional module API and `IsArtinianRing.of_finite` |
| 15704 | Every proper prime is maximal; in a primary quotient the radical is nilpotent and every element is a unit or zero-divisor | `IsArtinianRing.isMaximal_of_isPrime`, `IsArtinianRing.isNilpotent_nilradical`, `IsArtinianRing.isUnit_iff_mem_nonZeroDivisors`, `Ideal.isPrimary_iff` |
| 15706 | Every ideal has a unique finite product of pairwise comaximal primary components, and the quotient is their direct product | general primary decomposition is available through `Submodule.isLasker` and `IsLasker.exists_isMinimalPrimaryDecomposition`; CRT is `Ideal.quotientInfRingEquivPiQuotient`; the source-shaped Artinian uniqueness/comaximal-product package remains open |
| 15708–15763 | Orthogonal idempotents, componentwise multiplication, decomposition of every ideal, and additivity of ranks | derivable from CRT and product/basis APIs; `IsArtinianRing.equivPi` gives the reduced product-of-fields case |
| 15765–15778 | Scalar extension acts componentwise and can split a primary component | tensor-product/product and étale base-change infrastructure; no primary-component theorem in this wording |
| 15780 | Prime ideals of first and second kind are distinguished by separability of the finite residue extension | exact modern predicate `Algebra.IsSeparable` |

### §3: complete reducibility

| Source | Result | Mathlib coverage |
|---|---|---|
| 15788–15790 | Complete reducibility is equivalently a finite product of fields; first kind means every field factor is separable | `IsArtinianRing.equivPi` plus `Algebra.Etale.iff_exists_algEquiv_prod` |
| 15796–15804 | If a scalar extension is reduced, then the original algebra is reduced, by contracting its prime decomposition | derivable from faithful injectivity/reduced descent and `Ideal.comap_isPrime` |
| 15806–15808 | Scalar extension of a product of finite separable fields remains a product of finite separable fields | forward étale base change is exact |
| 15810–15826 | An inseparable field factor becomes nonreduced over the algebraic closure; Noether constructs a nonzero `G(γ)` with `G(γ)^p = 0` | separability and trace consequences exist; the explicit nilpotent-witness theorem is not packaged |
| 15839–15843 | All splitting idempotent coefficients lie in one finite extension `Ω/P`; the footnote characterizes a minimal such compositum of splitting fields | splitting-field APIs are ingredients; combined finite-Ω result open |

### §§4–5: matrix representations, classes, trace, and discriminant

| Source | Result | Mathlib coverage |
|---|---|---|
| 15856–15880 | Multiplication on an ideal gives a matrix representation with kernel `(0):a`, hence `R/((0):a)` is its matrix image | `Algebra.lmul`, `Algebra.leftMulMatrix`, and `RingHom.quotientKerEquivRange` cover regular multiplication; arbitrary ideal representations need packaging |
| 15882–15892 | Changing the ideal basis conjugates the matrix representation | exact change-of-basis matrix API; trace conjugation includes `Matrix.trace_units_conj` |
| 15894–15904 | Ideal classes correspond bijectively to the representation classes produced by ideals | no direct pinned formalization found; source-specific `GAP_CANDIDATE` |
| 15906–15910 | Class trace and norm are characteristic-polynomial coefficients; trace is `Σ`-linear; in a domain trace and norm are independent of the ideal class | `Algebra.trace`, `Algebra.norm`, and `Algebra.trace_eq_matrix_trace` are exact for the regular representation; class-parametrized variants are open |
| 15912–15920 | Basis change multiplies discriminant by a square of a unit; the generated principal discriminant ideal is invariant | `Algebra.discr_of_matrix_vecMul` and `Algebra.discr_of_matrix_mulVec` give the exact regular-basis formula |
| 15926–15932 | Direct sums of ideal classes induce direct sums of representation classes | source-specific packaging absent |
| 15936–15948 | Trace is additive over components and the discriminant ideal is the product of component discriminant ideals | `Algebra.trace_prod` is exact; discriminant multiplicativity follows from block determinants but has no dedicated `Algebra.discr_prod` declaration |
| 15972–15974 | Discriminant ideals extend under coefficient extension | general ideal statement is partial; localization is exact as `Algebra.discr_localizationLocalization` |

### §6: the trace-pairing criterion

| Source | Result | Mathlib coverage |
|---|---|---|
| 15982–15984 | Extend bases along the radical-power filtration of a primary algebra | standard basis-extension API; filtered choice is derivable |
| 15986 | Every element in the associated prime of a primary algebra has trace zero | derivable from nilpotence and `Algebra.isNilpotent_trace_of_isNilpotent`; over a field a nilpotent trace is zero |
| 15988 | A finite-dimensional domain over an algebraically closed field is the base field and has unit discriminant | Artinian-domain field theorem plus algebraic-closedness and the rank-one discriminant computation |
| 15990 | A proper primary algebra over an algebraically closed field has zero discriminant | proof ingredients exist, but no direct declaration was found |
| 15998–16017 | In the separable field case, trace is the sum of conjugates, norm their product, and discriminant the square of the embeddings determinant | `Algebra.trace_eq_sum_embeddings`, `Algebra.norm_eq_prod_embeddings_gen`, `Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two` |

### §§7–8: orders, quotients, and localization

| Source | Result | Mathlib coverage |
|---|---|---|
| 16028–16030 | A full order has a rank-`n` free basis, a basis-independent nonzero discriminant, and the conjugate-determinant formula | finite-free and discriminant APIs cover the constituent facts |
| 16032 | Every nonzero order ideal has a unique product of pairwise comaximal primary ideals | Lasker decomposition and CRT are constituents; exact one-dimensional order package open |
| 16034–16039 | `T/pT` has dimension `n` over `H/p`, with the order basis reducing to a residue basis | quotient-basis infrastructure; source statement is derivable |
| 16041 | `disc(T)` maps to the discriminant of `T/pT`; the factorization of `pT` maps to the zero-ideal decomposition | `Algebra.trace_quotient_mk` supplies the entrywise trace statement; the discriminant corollary is the smallest target below |
| 16043 | Primary and prime components correspond through the quotient, with isomorphic iterated quotients | quotient-ideal and CRT infrastructure |
| 16047 | Perfect residue field removes the inseparable-prime alternative; the maximal-order case is the square-prime criterion | arbitrary-order statement open; maximal-order statement modernly derivable |
| 16057–16059 | Multiplication-ring hypotheses; a multiplication ring with only one nonzero proper prime is a PID | modern Dedekind/PID results include `IsPrincipalIdealRing.of_finite_primes` |
| 16061–16065 | Relative trace and discriminant ideal generated by all rank-`n` trace determinants; finitely many minors generate it, and a free basis makes it principal | trace determinants exist; this general order discriminant ideal is not a pinned packaged definition |
| 16067–16069 | Ideals and residue rings correspond under localization; local equality at every prime detects global ideal equality | `IsLocalization.orderEmbedding`, `IsLocalization.orderIsoOfPrime`, and Dedekind factorization APIs |
| 16071–16073 | The localized order is finite free over a local PID and its discriminant generates the localized global discriminant ideal | `Module.Basis.localizationLocalization`, `Algebra.trace_localization`, `Algebra.discr_localizationLocalization`, and `IsDedekindDomain.isPrincipalIdealRing_localization_over_prime` |
| 16081 | A base prime divides the relative maximal-order discriminant iff some prime above it occurs to exponent at least two | modernly derivable through `differentIdeal`, `Ideal.relNorm`, unramifiedness, and ramification index |

## Exact pinned Mathlib anchors

The principal exact-revision sources and declarations are:

- [`Algebra.discr`, basis-change formulas, separable-field nonvanishing, and
  the embeddings determinant`](https://github.com/leanprover-community/mathlib4/blob/fabf563a7c95a166b8d7b6efca11c8b4dc9d911f/Mathlib/RingTheory/Discriminant.lean):
  `Algebra.discr`, `Algebra.discr_def`,
  `Algebra.discr_of_matrix_vecMul`, `Algebra.discr_of_matrix_mulVec`,
  `Algebra.discr_not_zero_of_basis`, and
  `Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two`.
- [`Trace/Defs.lean`](https://github.com/leanprover-community/mathlib4/blob/fabf563a7c95a166b8d7b6efca11c8b4dc9d911f/Mathlib/RingTheory/Trace/Defs.lean)
  and [`Trace/Basic.lean`](https://github.com/leanprover-community/mathlib4/blob/fabf563a7c95a166b8d7b6efca11c8b4dc9d911f/Mathlib/RingTheory/Trace/Basic.lean):
  `Algebra.trace`, `Algebra.trace_prod`, `Algebra.traceForm`,
  `Algebra.traceMatrix`, `Algebra.trace_eq_sum_embeddings`,
  `Algebra.trace_eq_zero_of_not_isSeparable`,
  `Algebra.traceForm_nondegenerate_tfae`, and
  `Algebra.isNilpotent_trace_of_isNilpotent`.
- [`Algebra.trace_quotient_mk`](https://github.com/leanprover-community/mathlib4/blob/fabf563a7c95a166b8d7b6efca11c8b4dc9d911f/Mathlib/RingTheory/Trace/Quotient.lean#L31-L50),
  for a finite free algebra over a local ring.
- [`Algebra.norm_eq_prod_embeddings_gen`](https://github.com/leanprover-community/mathlib4/blob/fabf563a7c95a166b8d7b6efca11c8b4dc9d911f/Mathlib/RingTheory/Norm/Basic.lean#L163-L181).
- [`Algebra.Etale.iff_exists_algEquiv_prod`](https://github.com/leanprover-community/mathlib4/blob/fabf563a7c95a166b8d7b6efca11c8b4dc9d911f/Mathlib/RingTheory/Etale/Field.lean#L268-L286),
  `Algebra.FormallyEtale.iff_exists_algEquiv_prod`, and
  `Algebra.FormallyEtale.equivPiOfIsSepClosed`.
- [`Algebra.Etale.baseChange`](https://github.com/leanprover-community/mathlib4/blob/fabf563a7c95a166b8d7b6efca11c8b4dc9d911f/Mathlib/RingTheory/Etale/Basic.lean#L248-L250).
- [`IsArtinianRing.equivPi`, prime-is-maximal, and nilradical
  results`](https://github.com/leanprover-community/mathlib4/blob/fabf563a7c95a166b8d7b6efca11c8b4dc9d911f/Mathlib/RingTheory/Artinian/Module.lean):
  `IsArtinianRing.isMaximal_of_isPrime`,
  `IsArtinianRing.equivPi`, and finite/Artinian transfer.
- [`Submodule.isLasker` and minimal primary decomposition`](https://github.com/leanprover-community/mathlib4/blob/fabf563a7c95a166b8d7b6efca11c8b4dc9d911f/Mathlib/RingTheory/Lasker.lean#L268-L308),
  with `IsLasker.exists_isMinimalPrimaryDecomposition`.
- [`Ideal.quotientInfRingEquivPiQuotient`](https://github.com/leanprover-community/mathlib4/blob/fabf563a7c95a166b8d7b6efca11c8b4dc9d911f/Mathlib/RingTheory/Ideal/Quotient/Operations.lean#L193-L248)
  and `Ideal.mul_eq_inf_of_isCoprime`.
- [`Module.Basis.localizationLocalization`](https://github.com/leanprover-community/mathlib4/blob/fabf563a7c95a166b8d7b6efca11c8b4dc9d911f/Mathlib/RingTheory/Localization/Module.lean#L161-L181),
  [`Algebra.trace_localization` and
  `Algebra.discr_localizationLocalization`](https://github.com/leanprover-community/mathlib4/blob/fabf563a7c95a166b8d7b6efca11c8b4dc9d911f/Mathlib/RingTheory/Localization/NormTrace.lean#L81-L120),
  and `IsLocalization.orderIsoOfPrime`.
- Dedekind factorization/localization:
  `Ideal.finprod_heightOneSpectrum_factorization`,
  `IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain`, and
  `IsDedekindDomain.isPrincipalIdealRing_localization_over_prime`.
- [`differentIdeal`, `not_dvd_differentIdeal_iff`, and
  `dvd_differentIdeal_iff`](https://github.com/leanprover-community/mathlib4/blob/fabf563a7c95a166b8d7b6efca11c8b4dc9d911f/Mathlib/RingTheory/DedekindDomain/Different.lean#L909-L960).
- [`NumberField.not_dvd_discr_iff_forall_mem`](https://github.com/leanprover-community/mathlib4/blob/fabf563a7c95a166b8d7b6efca11c8b4dc9d911f/Mathlib/NumberTheory/NumberField/Discriminant/Different.lean#L174-L203),
  `Ideal.ramificationIdx_ne_one_iff`, and
  `Algebra.isUnramifiedAt_iff_of_isDedekindDomain`.
- [`Ideal.relNorm`](https://github.com/leanprover-community/mathlib4/blob/fabf563a7c95a166b8d7b6efca11c8b4dc9d911f/Mathlib/RingTheory/Ideal/Norm/RelNorm.lean#L267-L305)
  and its prime/factorization formulas.

These anchors are modern encodings. They do not by themselves constitute the
arbitrary-order discriminant theorem.

## Exact étale-descent warning

The reverse direction of the tempting modern scalar-extension equivalence
must **not** be advertised as axiom-free at the pinned revision.

[`Mathlib/RingTheory/Etale/Descent.lean`](https://github.com/leanprover-community/mathlib4/blob/fabf563a7c95a166b8d7b6efca11c8b4dc9d911f/Mathlib/RingTheory/Etale/Descent.lean#L56)
declares
`Algebra.Etale.of_etale_tensorProduct_of_faithfullyFlat`, but its dependency
chain passes through

```lean
proof_wanted FormallySmooth.of_formallySmooth_tensorProduct_of_faithfullyFlat
```

at exact-revision source line 56. `Smooth.of_smooth_tensorProduct_of_faithfullyFlat`
uses that declaration, and `Etale.of_etale_tensorProduct_of_faithfullyFlat`
then uses the smooth result at lines 85–88. Thus this reverse descent theorem
is present as an API declaration but is not an axiom-free proof of Noether's
§3.2 theorem in Mathlib `v4.31.0`.

A bounded scan of the named central source files above found no other
`proof_wanted`, `sorry`, or explicit `sorryAx` occurrence. That is a static
source observation, not `#print axioms` evidence: no Lean build was authorized
or run for this audit.

## Dependency graph

Noether's proof has the following central dependency chain:

```text
finite order T/H with basis a₁,…,aₙ
  ├─ reduce basis modulo p                         16034–16039
  ├─ trace and discriminant reduce modulo p       16041
  └─ primary factors of pT become factors of (0)  16043
                         │
                         v
finite-dimensional residue algebra R = T/pT
  ├─ Artinian primary/product decomposition       15700–15778
  ├─ separable versus inseparable field factors   15780–15828
  └─ nonzero discriminant iff separable product   15982–15994
                         │
                         v
p divides disc(T)
  iff R is not a product of separable fields
  iff pT has a proper primary component or inseparable prime 16045–16049
```

The modern pinned dependency graph for the smallest bridge is:

```text
Algebra.trace_quotient_mk
  + Algebra.traceMatrix / Algebra.discr_def
  + RingHom.map_det
  + basisQuotient
        |
        v
Algebra.discr_quotient_mk            proposed small target
        |
        +-- IsLasker primary decomposition + CRT
        +-- finite-algebra discriminant/étale criterion   still open
        v
source-shaped order discriminant theorem                 later target
```

For maximal orders, a separate modern route is already available:

```text
NumberField.not_dvd_discr_iff_forall_mem
  -> Algebra.IsUnramifiedAt
  -> ramification index = 1
  -> not (map p ≤ P^2)
```

That route must not be conflated with Noether's stronger theorem for arbitrary
orders, where non-prime primary components detect the failure of maximal-order
factorization.

## Promoted local quotient-discriminant theorem

The smallest reusable source-facing target is now promoted as the discriminant
corollary of `Algebra.trace_quotient_mk`, corresponding to line 16041. With
`p = IsLocalRing.maximalIdeal R`, it is:

```lean
theorem discr_basisQuotient
    {R S ι : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [IsLocalRing R] [Module.Free R S] [Module.Finite R S]
    [Fintype ι] [DecidableEq ι] (b : Basis ι R S) :
    Algebra.discr (R ⧸ IsLocalRing.maximalIdeal R) (basisQuotient b) =
      Ideal.Quotient.mk (IsLocalRing.maximalIdeal R) (Algebra.discr R b)
```

The proof:

1. unfold `Algebra.discr_def` on both sides;
2. prove the trace matrices agree entrywise after applying the quotient map,
   using `Algebra.trace_quotient_mk` and preservation of multiplication;
3. finish with `RingHom.map_det`.

This theorem is preferable to starting with the complete order theorem: it is
central to Noether's argument, independent of a particular primary
decomposition package, reusable for local arithmetic, and avoids the
unfinished étale-descent dependency. It is canonical in
`MathematicalCommons/Noether/DiscriminantTheorem1927.lean`. The direct bounded
Lean 4.31 check exited zero with empty stderr, unchanged source, and a
1,555,980,288-byte peak. `#print axioms` reports exactly `propext`,
`Classical.choice`, and `Quot.sound`; receipt
`artifacts/build/DiscriminantTheorem1927-20260825T0157441688080-096019d5.receipt.json`.

## Authorial qualifications and QA risks

### Authorial qualifications to preserve

- **15610:** finite-order and commutative-ring conventions.
- **15618:** the imperfect-residue-field distinction is essential; deleting
  the second-kind alternative changes the theorem.
- **15620:** Noether explicitly calls an earlier Festschrift formulation
  erroneous. This is an authorial historical correction, not a transcription
  discrepancy.
- **15622–15624:** the module-basis method deliberately avoids primitive-element
  and power-basis failures after reduction.
- **15626:** the proposed composition-length ramification theory is
  prospective, not proved here.
- **15642, 15681:** equivalent disjoint copies are essential to Noether's
  concrete scalar-extension construction, which can create zero-divisors.
- **15843:** the footnote's minimal `Ω` is a compositum of splitting/Galois
  fields; the main corollary only needs existence of some finite `Ω`.
- **15896:** the paper does not ask whether every homomorphic matrix ring comes
  from an ideal.
- **15930:** the converse from direct-sum representation classes to direct-sum
  ideal classes is explicitly left open.
- **16017:** `R` is only equivalent to the conjugate fields `Kᵢ`; it is not
  assumed literally embedded in `Ω`.
- **16045:** the function-field example stresses that an inseparable residue
  extension need not be simple.
- **16047:** the square-prime specialization requires a perfect residue field
  and the maximal order.
- **16067, 16071:** localization results and the finite-free local-order fact
  are referred to Grell rather than reproved.
- **16073:** identification with Hilbert's relative discriminant is made in a
  footnote through equality after every localization.

### Controlled-source QA resolution

Primary-witness and contextual review has closed all three reported items:

1. Seven basis-index glyphs were accepted as `R_{\bar a}` in ED0019 and are
   inherited by inactive successor ED0020. This is a notation correction, not
   a change to the conjugacy argument.
2. The `u` at line 16045 is introduced by the cited function-domain
   construction; no variable or coefficient phrase is missing.
3. The cross-reference at line 16073 was accepted as “nach 2.” in ED0019 and
   is inherited by ED0020.

Existing declarations and source locators remain bound to the immutable ED0014
witness until an explicit canon rebase; ED0020 is not treated as active here.

The following are **not** QA defects:

- historical reversed ideal-divisibility notation;
- `Quotientenring` meaning localization in §8;
- the closing date 1926 for a 1927 publication;
- Noether's informal “no cross-relations” presentation of tensor-product
  scalar extension; and
- the explicit warning that the earlier Festschrift theorem was wrong.

## Audit and build state

P31 remains a partial source/Mathlib audit, but it now includes the canonical,
green quotient-discriminant theorem described above. The arbitrary-order and
relative-order theorems remain gaps, and the reverse étale-descent route is not
axiom-free at the pinned revision. No Git or Lake command was run. The promoted
proof used the direct one-thread 5 GiB checker against the declared
`v4.31.0`/`fabf563...` snapshot.
