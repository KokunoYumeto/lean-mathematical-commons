# Hentzelt--Noether 1923: polynomial ideals and resultants

## Provenance and attribution

- Work packet: P22, controlled lines 12702--13515.
- Publication: *Mathematische Annalen* 88 (1923), pp. 53--79.
- Controlled witness: `NOETH-DE-AUTH-v052-20260815` / `ED0014_R785`,
  SHA-256
  `EE226847656BC4D65EDDA9E9BF9BB1D25797C0C6D672D267D94A97FD88C7AD58`.
- Baseline: Lean 4.31.0; Mathlib `v4.31.0`, commit
  `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`.

The heading and the editorial footnote at line 12719 fix the attribution.
The mathematics and original proofs are Kurt Hentzelt's. Emmy Noether describes
the paper as her completely free conceptual recasting of the essential part of
his dissertation. This audit therefore uses **Hentzelt--Noether** for the
edited paper and does not turn its results into uncomplicated sole-Noether
theorems.

## Source architecture

The paper is genuinely staged. For each variable level `i`, a polynomial ideal
is regarded as a module of linear forms in the earlier monomials. A finite
module model supplies elementary divisors and a determinant norm. Definition
VI then sets

```text
R_m = R^(1) * ... * R^(n),    E_m = E^(1) * ... * E^(n).
```

The factors `R^(i)` are stage resultants, not repeated occurrences of one
ordinary univariate `Polynomial.resultant`. This confirms the canon owner's
resolution of P18's compressed product display.

## Claim-level Mathlib map

| Source | Claim | Pinned Mathlib anchors | Coverage boundary |
|---|---|---|---|
| 12712--12720 | elimination problem and two-part main result | `MvPolynomial.zeroLocus`; ideal order | Common-zero semantics are exact; construction, multiplicity, and injectivity of the resultant form remain gaps. |
| 12752, Definition I | ground module: no proper divisor of equal rank | `Submodule`; `Module.rank`; module torsion and saturation | Formula (2)'s cancellation condition and formula (4)'s nonzero-scalar saturation are promoted, with the least-ground-module and same-rank consequences. The exact equivalence with every nuance of the historical no-proper-divisor phrasing is not separately packaged. |
| 12763--12795, Satz I | unique smallest ground-module divisor of equal rank | submodule saturation; torsion quotients; rank-nullity | The formula-(4) least-ground-module construction and basis-independent same-rank theorem are promoted. A displayed Smith-basis representation over the historical coefficient ring belongs to the later localization/Smith bridge. |
| 12800--12810, Definition II | scalar quotient of two linear-form modules | `Submodule.colon`; `Submodule.mem_colon` | The modern interpretation is now explicit: `A.colon (B : Set E)` is the ideal of scalars carrying `B` into `A`. This fixes the orientation used in the promoted first-stage formulas; it does not assert that every historical slash denotes a module quotient. |
| 12815--12844, Satz II | reciprocal relation with the highest elementary divisor | `Submodule.smithNormalFormCoeffs`; `Ideal.smithCoeffs` | The first localized Smith pair now has exact scalar-colon formulas. Its quotient by the whole ground module is an infimum of the remaining principal coefficient ideals, and it reduces to one principal ideal only under an explicit greatest-remaining-divisor hypothesis. The historical highest-elementary-divisor ordering itself is still not proved. |
| 12849--12895, Satz III | quotient representation over a polynomial/domain coefficient ring | localization and fraction-field APIs | The generalized statement is a gap; it cannot be inferred merely from PID Smith form. |
| 12906--12918, Definition III | norm as determinant of the transition from ground module to module | `LinearMap.det`; `Algebra.norm_eq_matrix_det`; Smith bases | Modern determinant norms give the right language after finite-free hypotheses are reconstructed. |
| 12919--12922, Satz IV | equal norm plus divisibility and equal rank imply module equality | determinant and Smith-normal-form APIs | No exact pinned declaration was found; equality of determinants alone is insufficient without the source's divisibility structure. |
| 12924--12998, Satz V | coprime factorization of a norm gives unique module factors | `IsCoprime`; Chinese-remainder and Smith infrastructure | The source-specific module reconstruction is missing. |
| 13004--13037, equation (12) and Definition IV | transformed ideals under the full lower-unitriangular generic coordinate matrix `U` | `MvPolynomial.bind₁`; algebra equivalences; homogeneous components; algebraic independence; ideal maps | The full family `y_μ = x_μ + Σ_{ν<μ} u_{μν}x_ν`, its recursive inverse, ideal transport, exact total-degree preservation, generic leading-coefficient nonvanishing, and existence of a regular member in every nonzero transformed ideal are promoted. Characteristic-zero descent to an actual finite ground-field lower-unitriangular equivalence is also promoted. The successive later-stage regular elements remain. |
| 13046--13055, Definition V | successive ground ideals | localization extension/contraction; local `groundIdealAlong` | The literal submonoid of nonzero polynomials free of the earlier variables, its source/zero-based indexing dictionary, equation-(16) membership, and stage antitonicity are promoted. |
| 13057--13107, Satz VI | ground ideals of transformed ideals are transformed | relative Dedekind--Mertens; bounded Kronecker substitution; parameter localization | Equation (17), simultaneous common-denominator presentations, coefficient reconstruction, late-variable preservation, and the final two-sided transformed-contraction equality are promoted with no primary or saturation hypothesis. |
| 13123--13319, Satz VII; equations (21)--(24) at 13134--13173 | infinite monomial module reduces to a finite module; only finitely many elementary divisors are nonunits | finite-free, localization, Smith-normal-form, monic polynomial division, submodule sums, torsion, rank-nullity, Finsupp bases, and polynomial-evaluation APIs | Equations (21)--(23) are promoted for a supplied degree-`k` polynomial regular in `x₁`: exact bounded representatives, their `Fin k` coefficient vectors, the internal decomposition of every containing ideal into its bounded part and disjoint principal tail, the finite free quotient, the abstract common-tail equivalence, its concrete paired-ideal specialization, and the actual cutoff-one ground-ideal quotient. A source-modeled cutoff-one `ξ`/`ζ` coordinate module realizes that ideal pair and connects its quotient to the bounded model. Line 13162 is exact: `G₁*` is the nonzero-scalar saturation of `M₁*`, its relative quotient is torsion, and the relative denominator has equal rank and `finrank`. The source-faithful map `P[x₃,…][x₂] → Frac(P[x₃,…])[x₂]` localizes only later-variable coefficients, commutes with the finite-coordinate saturation, and yields the actual localized pair and its equal-`finrank` denominator. The finite cutoff-one pair has a localized Smith instance with selected bases, diagonal coefficients, cyclic quotient, and determinant product. A freely adjoined arbitrary Finsupp tail, with a countable `ℕ` specialization, now models the printed independent `ζ` coordinates: numerator and denominator receive the same tail basis, every tail coefficient is `1`, the tail cancels, and the finite cyclic quotient is recovered. Identification with a separately constructed and localized historical unbounded `ζ`-module, canonical divisibility ordering, any infinite determinant, determinant norm/resultant identification, historical/canonical primitive-form identification and choice independence, and later stages remain open. |
| 13153--13160, equation (23) | isomorphism of residue-class systems after adjoining the same independent tail | `LinearMap.quotientInfEquivSupQuotient`; `Submodule.Quotient.equiv`; Finsupp modules; product submodules; `LinearEquiv` | The abstract equivalence and its product-head helpers are `NEW_PACKAGING` of Mathlib quotient equivalences, with divisibility oriented as denominator `M ≤ G`. The actual localized cutoff-one pair is now a `FORMALIZED_GAP` instantiation with an arbitrary freely adjoined Finsupp tail and a countable specialization; the resulting quotient cancels that shared tail and recovers the finite localized pair. This does not yet identify the free tail with a separately constructed/localized historical unbounded module. |
| 13164--13173, equation (24); 13323--13335, Definition VI | diagonal basis presentation, stage resultants, elementary-divisor forms, and their products | Smith bases/coefficients; `Submodule.quotientEquivPiSpan`; module annihilators; finite ideal products; `Matrix.det_diagonal`; polynomial localization | Generic full-rank finite-free PID `NEW_PACKAGING` supplies the diagonal and cyclic-quotient scaffold plus a chosen-basis determinant product. The historical localization of only `P[x₃,…]` to `K = Frac(P[x₃,…])`, fixing `x₂`, and the corresponding finite cutoff-one Smith instance over `K[x₂]` are `FORMALIZED_GAP`. The intrinsic annihilator of that quotient is identified with the intersection of the selected coefficient ideals and with the denominator scalar colon. If `D` is the selected coefficient product and `A` this annihilator, then `(D) ≤ A` and `A^ρ ≤ (D)`; over the PID their chosen generators satisfy both corresponding divisibilities and have equal radicals. Under the explicit `IsGreatestRemainingDivisor` hypothesis for a selected `eᵢ`, the library also identifies `A = (eᵢ)`, proves `eᵢ ∣ D`, `D ∣ eᵢ^ρ`, and packages the radical and vanishing bridges for the actual localized pair. That selected coefficient has a nonzero integral numerator. Given the regular member used in the finite reduction, regular division lifts its bounded denominator action to every element of the cutoff-one ground ideal and produces the full `HasEquation33Witness I 1` with a genuine cutoff-two multiplier. The library does not prove that a greatest index exists or impose a canonical divisibility order. The source-instantiated common-tail module still uses a freely adjoined identity tail. Historical-tail identification, determinant norm/resultant identification, later Smith stages, historical/canonical primitive-form identification, and choice independence remain open. |
| 13340--13382, Satz VIII | `E_m ∣ R_m`, `R_m ∣ E_m^N`, and tail products annihilate ground ideals modulo `m` | module annihilators; principal ideal products and powers; ideal radicals and evaluation; localization contraction; colon ideals; Noetherian finite generation | The intrinsic opening bounds and conditional greatest-coefficient bridge are promoted for the actual cutoff-one Smith quotient. Localization surjectivity supplies a nonzero integral numerator for the selected greatest coefficient, and regular division now promotes its bounded action to the full cutoff-one equation-(33) witness: for every `g ∈ stageGroundIdeal 1 I`, a nonzero multiplier free of the first two variables sends `E * g` into `I`. The selected cutoff-one coefficient/product proxies now have primitive nonzero integral representatives that retain both integral divisibilities and equation-(33) witnesses, but they are not identified with the historical `E^(2)` or `R^(2)`, canonical, or choice-independent. Equation (33)'s generic one-stage descent and Noetherian common-multiplier theorem remain available, and a supplied consecutive witness family is iterated through arbitrary finite windows to prove the terminal identity and conditional `E`-product half of equation (34). Later-stage witnesses are still supplied rather than constructed, and the parallel historical `R^(i)` product and determinant-norm/resultant identification remain open. |
| 13387--13400, Satz IX | a divisor ideal with the same resultant form equals the original ideal | ideal order; stage norms | This depends on Satz IV at every stage and has no end-to-end pinned theorem. |
| 13405--13417, Satz X | coprime factorization of one stage resultant gives unique ideal factors | comaximal ideals; Chinese remainder; colon ideals | The reconstruction of the two historical ideal factors and their least-common-multiple statement remains a gap. |
| 13426--13428, Satz XI | rank of the image of a univariate ideal modulo a member `h` is `deg h - deg f` | PID structure; `finrank_quotient_span_eq_natDegree` | The exact residue-ideal rank theorem, quotient equivalence, and displayed basis represented by `f, Xf, ..., X^(deg h₁-1)f` are promoted with necessary nonzero hypotheses. |
| 13430--13440 | successive determinantal elimination ideals | matrices, minors, Fitting-ideal substrate | Independence of the chosen regular polynomial and the complete staged construction remain gaps. |
| 13443--13445, Satz XII | the last nonzero stage gives finitely many compatible partial zeros; no zero implies the unit ideal | finite root sets, products of finite sets, and Nullstellensatz APIs | The coordinatewise finite-root-box containment and explicit zero-locus embedding are promoted whenever the ideal contains one nonzero univariate polynomial in each coordinate, as is the exact algebraically-closed-field equivalence `zeroLocus = ∅ ↔ I = ⊤`. The stronger stagewise compatibility theorem remains missing. |
| 13447--13462 | generic linear form separates compatible tuples and factors explicitly | splitting fields; polynomial factorization | The basis-independent compatible-tuple factorization is a substantial elimination bridge. |
| 13493--13506, Satz XIII | each linear factor of a stage resultant extends uniquely to a compatible zero; exponents equal residue dimensions | splitting, quotient, and finrank APIs | Unique extension, factor/ideal correspondence, and multiplicity identification remain gaps. |
| 13508 | characteristic-zero specialization preserving regularity and gcd normalization | polynomial specialization and primitive-part APIs | Simultaneous preservation of any supplied finite family of regularity witnesses is promoted after polynomial denominator clearing; preservation of primitive, gcd, and resultant normalizations remains open. |

## Promoted Satz VIII support

The canonical module
`MathematicalCommons/Noether/PolynomialIdealsAndResultants1923.lean` proves
four consequences under the two divisibility hypotheses of Satz VIII:

- equality of the radicals of the principal ideals generated by `R` and `E`;
- vanishing equivalence after every ring map into a field;
- its multivariate evaluation specialization; and
- equality of the corresponding pointwise vanishing sets.

This is deliberately conditional. It does **not** claim that Mathlib already
constructs `R^(i)` or `E^(i)`, and it does not assume their divisibilities as
axioms. The direct Lean 4.31 build exited zero with empty stderr and unchanged
source, observed 1,363,025,920 bytes peak under the 2.5 GiB watcher, and all 51
declarations in the expanded module report only `propext`, `Classical.choice`,
and `Quot.sound`. Receipt:
`artifacts/build/MathematicalCommons-Noether-PolynomialIdealsAndResultants1923-20260825T1601284397517-047344cb.module.receipt.json`.

The finite localized opening of Satz VIII is now unconditional in an
intrinsic form. For the actual equation-(24) quotient, put

```text
A = Ann(G₁*/M₁*) = ⋂ᵢ (eᵢ),       D = ∏ᵢ eᵢ.
```

Then `(D) ≤ A` and `A^ρ ≤ (D)`. If `a` is Mathlib's chosen generator of the
principal ideal `A`, this gives `a ∣ D` and `D ∣ a^ρ`, hence equal radicals.
This avoids silently imposing a divisibility order on Mathlib's selected
Smith coefficients. It is not yet the historical claim that primitive
`E^(i)` and `R^(i)` enjoy those divisibilities: later-stage equation-(33)
witness construction, identification of the selected primitive proxies with
the historical forms, the parallel `R^(i)` product, and
determinant-norm/resultant identification still block the complete equation
(34).

## Dedekind--Mertens and equation (17)

Lines 13059--13077 state the coefficient-module identity

```text
A^q B = A^(q-1) C,
```

where `A` and `B` are the additive modules of integer-linear combinations of
the coefficients of two multivariate polynomials and `C` is the corresponding
module for their product. The pinned Mathlib source
`Mathlib/RingTheory/Polynomial/ContentIdeal.lean` contains the modern content
ideal and weaker inclusions, but its module documentation explicitly lists
general Dedekind--Mertens as future work.

The canonical module first proves, over every commutative ring,

```text
c(f)^(natDegree(g)+1) c(g) = c(f)^natDegree(g) c(fg).
```

The hard containment is first proved for every formal degree bound `m`:

```text
c(f)^(m+1) c(g) <= c(f)^m c(fg)    when natDegree(g) <= m.
```

The proof erases the top coefficient of `g`, applies the induction hypothesis,
uses a descending convolution argument for the coefficients of `f`, and then
uses colon ideals to lift the coefficientwise containments to the full content
ideal. Mathlib's existing easy containment supplies the reverse inclusion.
This handles zero and sparse polynomials without a separate nonzero
hypothesis. The earlier direct degree-one proof and equation (17)-shaped
witness `q = 2` remain available as source-readable corollaries.

The same proof is generalized to `coefficientModule (A := A)` for every
commutative algebra `A → R`. At `A = R` it is definitionally the content ideal;
at `A = ℤ` it has exactly Hentzelt's integer-linear semantics. The `Kronecker`
namespace then constructs a bounded injective encoding of finite-variable
monomials, proves support and coefficient-finset preservation, and transports
the univariate theorem back to multivariate polynomials. Consequently
`exists_dedekindMertens_mvCoefficientModule` proves equation (17) literally:

```text
there is q ≥ 1 with M(f)^q M(g) = M(f)^(q-1) M(fg).
```

The application lemmas also formalize the algebraic inference used in
equations (19)--(20): coefficient containment of `Φ^q Γ` yields membership of
`Φ^q * C(γ)` in the extended ideal. Three additional canonical modules now
complete the surrounding one-direction bridge:

- `CoordinateTransform.lean` constructs the full lower-unitriangular equation
  (12), its recursive inverse, and transport of ideals and generating sets;
- `LocalizationBridge.lean` swaps the two nested variable sets, identifies the
  direct and two-stage ideal extensions, and clears an arbitrary rational-
  function member with one nonzero polynomial in the parameters; and
- `SatzVIBridge.lean` packages the rational-function transform, the witness
  form of the stage ground ideal, and proves
  `parameterCoefficient_mem_groundIdealAlong`, the abstract (19)→(20) step.

These modules add 81 declarations, each with a matching axiom audit. Their
canonical builds exited zero with empty stderr and respective peaks
1,194,127,360, 1,308,258,304, and 1,271,476,224 bytes. Receipts:
`artifacts/build/MathematicalCommons-Noether-PolynomialIdealsAndResultants1923-CoordinateTransform-20260825T1624088070279-fccc754f.module.receipt.json`,
`artifacts/build/MathematicalCommons-Noether-PolynomialIdealsAndResultants1923-LocalizationBridge-20260825T1624219625650-40a6478e.module.receipt.json`, and
`artifacts/build/MathematicalCommons-Noether-PolynomialIdealsAndResultants1923-SatzVIBridge-20260825T1625164741096-8cf64eb2.module.receipt.json`.

Five further canonical modules add 36 declarations and close that equality:

- `FiniteParameterBridge.lean` transports equation (17) and the coefficient
  bridge from `Fin m` to an arbitrary finite parameter type without exposing
  an enumeration;
- `GenericParameters.lean` indexes the printed coefficients by the literal
  subtype of pairs `(μ,ν)` with `ν<μ`, proves those fraction-field
  coefficients algebraically independent, and instantiates equation (12)
  directly;
- `StageMultipliers.lean` defines the nonzero late-variable submonoid and the
  exact equation-(16) stage ground ideal, including the one-based source to
  zero-based Lean index conversion;
- `SatzVIReverse.lean` absorbs parameter denominators, reconstructs all
  transformed coefficients, and cancels only genuine nonzero field scalars;
  and
- `SatzVICommonPresentation.lean` gives two rational-function polynomials one
  common parameter denominator, proves the hard reverse inclusion, and proves
  `stageGroundIdeal_genericTransform_eq`, together with the direct
  lower-pair-parameter specialization
  `stageGroundIdeal_independentLowerUnitriangular_eq`.

Their clean canonical receipts are
`artifacts/build/MathematicalCommons-Noether-PolynomialIdealsAndResultants1923-FiniteParameterBridge-20260825T1712262015996-f20325d6.module.receipt.json`,
`artifacts/build/MathematicalCommons-Noether-PolynomialIdealsAndResultants1923-GenericParameters-20260825T1713256603826-8eceb7ac.module.receipt.json`,
`artifacts/build/MathematicalCommons-Noether-PolynomialIdealsAndResultants1923-StageMultipliers-20260825T1652079444030-a9aaebc0.module.receipt.json`,
`artifacts/build/MathematicalCommons-Noether-PolynomialIdealsAndResultants1923-SatzVIReverse-20260825T1724082534888-c424b8f0.module.receipt.json`, and
`artifacts/build/MathematicalCommons-Noether-PolynomialIdealsAndResultants1923-SatzVICommonPresentation-20260825T1724217884888-614bc32e.module.receipt.json`.
The respective observed peaks are 1,270,198,272, 1,301,225,472,
1,295,699,968, 1,294,675,968, and 1,297,661,952 bytes. Every declaration has
a matching axiom audit and reports only `propext`, `Classical.choice`, and
`Quot.sound`.

Thus Satz VI's source claim—a ground ideal of the generic transform is itself
the transform of its contraction—is formalized in both directions. The
regularity determinants used later to guarantee suitable polynomials at every
stage are separate downstream infrastructure, not a missing hypothesis of
this equality.

## Satz XI and the finite-zero substrate for Satz XII

`SatzXI.lean` adds twelve declarations. It defines the residue ideal of `(f)`
inside `K[X]/(h)`, proves its rank is `natDegree h - natDegree f`, identifies
it with `K[X]/(h₁)` when `h=h₁f`, and constructs the exact basis represented
by `f, Xf, ..., X^(natDegree h₁-1)f`. The necessary assumptions `f ≠ 0` and
`h₁ ≠ 0` are explicit. Its clean receipt is
`artifacts/build/MathematicalCommons-Noether-PolynomialIdealsAndResultants1923-SatzXI-20260825T1654276582795-90e47005.module.receipt.json`
with 1,362,034,688 bytes observed peak.

`SatzXII.lean` adds eight declarations. Seven formalize the finite-coordinate
substrate: embedding a univariate polynomial into one coordinate, its
evaluation identity, containment of every common zero in the product of the
coordinate root sets, an explicit injection into that finite product, and two
forms of zero-locus finiteness. This direction needs no algebraic-closedness
hypothesis. The eighth theorem proves the exact corollary immediately following
Satz XII: over an algebraically closed extension field and finitely many
variables, `zeroLocus = ∅` iff the ideal is `⊤`. Its clean receipt is
`artifacts/build/MathematicalCommons-Noether-PolynomialIdealsAndResultants1923-SatzXII-20260825T1728308694524-fa5e2a5e.module.receipt.json`
with 1,365,041,152 bytes observed peak. This deliberately does not claim the
still-open stagewise construction of compatible partial zeros.

Across the base module and its first ten P22 support modules, this checkpoint
contained 188 declarations with matching axiom audits.

## Characteristic-zero regularity specialization

`RegularitySpecialization.lean` adds eight declarations. It formalizes the
source definition that a degree-`r` polynomial is regular in `x_i` when its
pure `x_i^r` coefficient is nonzero; proves that a nonzero multivariate
polynomial over an infinite domain has a nonvanishing evaluation; packages
simultaneous avoidance for finite sets and arbitrary `Fintype` families; and
shows that one characteristic-zero specialization preserves a supplied finite
family of regularity witnesses. The clean canonical receipt is
`artifacts/build/MathematicalCommons-Noether-PolynomialIdealsAndResultants1923-RegularitySpecialization-20260825T2235544405991-6ed747de.module.receipt.json`
with 1,190,191,104 bytes observed peak.

This is the exact finite-avoidance layer used by the specialization paragraph
at line 13319 after polynomial denominator clearing. It does not construct the
determinants `C^(i)`, prove their leading parameter polynomials nonzero, choose
representatives for rational-function coefficients, or preserve the later gcd
and resultant normalizations. At the preceding specialization checkpoint P22 had 196 canonical
declarations across the base and eleven support modules.

## Equation (21): division by a regular polynomial

`RegularityDivision.lean` adds twelve declarations. It converts the pure-power
regularity condition into exact leading-coefficient and univariate-degree facts
under `MvPolynomial.finSuccEquiv`, scales the supplied regular divisor to a monic
polynomial, defines its quotient and remainder, proves the strict
remainder-degree bound, and reconstructs the original polynomial exactly. It
then transports this construction back to a multivariate bounded
representative, proving that every polynomial is congruent modulo the regular
divisor to one whose `x₁`-degree is strictly less than `k`.

The clean canonical receipt is
`artifacts/build/MathematicalCommons-Noether-PolynomialIdealsAndResultants1923-RegularityDivision-20260826T0008290451725-a4fbcf99.module.receipt.json`,
with 1,212,952,576 bytes observed peak. All twelve declarations have matching
axiom audits and use only `propext`, `Classical.choice`, and `Quot.sound`.

This formalizes equation (21) for one supplied regular divisor over a field. It
does not construct `C^(1)` from the transformed ideal, construct the later
`C^(i)`, assemble the finite stage modules or their Smith data, or prove
independence from auxiliary regular-polynomial choices. At the preceding
regular-division checkpoint P22 had 208
canonical declarations across the base and twelve support modules.

## Equations (22)--(23): bounded parts and the common tail

`RegularIdealDecomposition.lean` adds eight declarations. It defines the
bounded part of an ideal in the univariate-over-the-remaining-variables model,
defines the principal tail generated by the supplied regular polynomial, proves
that regular remainders of ideal members stay in the ideal, extracts the exact
`Fin k` coefficient vector displayed in equation (22), and proves equation
(23): every ideal containing the regular divisor is the sum of its bounded part
and that principal tail.

`RegularTailDisjoint.lean` adds five more declarations. It proves that scaling
the regular divisor to monic form does not change its principal tail and then
uses the strict degree bound to show that the bounded part and principal tail
are disjoint. Thus equation (23) is an internal sum, matching the independence
argument at lines 13149--13160.

The clean canonical receipts are
`artifacts/build/MathematicalCommons-Noether-PolynomialIdealsAndResultants1923-RegularIdealDecomposition-20260826T0116271374572-83ecc6d8.module.receipt.json`
(1,260,863,488 bytes peak) and
`artifacts/build/MathematicalCommons-Noether-PolynomialIdealsAndResultants1923-RegularTailDisjoint-20260826T0126104705129-52db92ff.module.receipt.json`
(1,227,345,920 bytes peak). All thirteen declarations have matching axiom
audits and use only `propext`, `Classical.choice`, and `Quot.sound`.

This layer models a polynomial ideal over the remaining-variable coefficient
ring. It does not yet construct Noether's regular `C^(1)`, identify the exact
historical linear-form modules `G₁` and `M₁`, prove their quotient isomorphism,
or assemble the inductive finite stage and its Smith data. At this equations-
(22)--(23) checkpoint P22 had 221 canonical declarations across the base and
fourteen support modules, and its ledger had 28 claim/definition records after
splitting those equations from the surrounding Satz-VII row.

## Equation (12): generic regularity and finite specialization

`GenericRegularity.lean` now contains 62 declarations over the independent
lower-triangular parameter field used for the source-faithful coordinate
change. In addition to the coordinate equivalence and homogeneous-degree
lemmas, it dehomogenizes a homogeneous polynomial by setting the first
coordinate to one and proves this operation injective at fixed degree. The
generic pure first-variable coefficient is the resulting polynomial evaluated
at the algebraically independent first-column parameters, so it is nonzero for
every nonzero homogeneous input.

Taking the nonzero top homogeneous component extends the result to every
nonzero polynomial. The generic transform preserves its exact total degree and
is regular in the first variable. At ideal level, the generic transform of
every nonzero ideal contains such a regular member. This closes the construction
that the earlier scaffold had left conditional.

The transform is then reconstructed over the polynomial parameter ring. Its
leading parameter coefficient is nonzero before localization, so the promoted
finite-avoidance theorem supplies one characteristic-zero ground-field
assignment preserving any supplied finite family of regular inputs. The
evaluated transform is proved equal to the corresponding lower-unitriangular
algebra equivalence; ideal membership is therefore both preserved and
reflected. In particular, every nonzero ideal has an actual finite specialized
coordinate transform containing a first-variable regular member.

The clean canonical receipt is
`artifacts/build/MathematicalCommons-Noether-PolynomialIdealsAndResultants1923-GenericRegularity-20260826T0529029977091-d53d82d9.module.receipt.json`,
with 1,492,131,840 bytes observed peak. All 44 theorem declarations have
matching axiom audits and use only `propext`, `Classical.choice`, and
`Quot.sound`; the other eighteen declarations are definitions or abbreviations.
The claim receipt is
`artifacts/build/claim-P22-finite-regularity-specialization-20260826T0527205736234-11e8edb4.json`.
## Equations (21)--(23): finite regular and common-tail quotients

`RegularQuotient.lean` packages the finite-module conclusion needed after
regular division. For a supplied polynomial regular of first-variable degree
`k`, the degree-below-`k` representatives and the principal tail are proved to
be complementary submodules. Consequently the ambient polynomial module
modulo that tail is linearly equivalent both to `Polynomial.degreeLT R k` and
to the `k`-entry coefficient space `Fin k → R`, where `R` is the polynomial
ring in the remaining variables. An explicit basis proves that quotient free
and finite over `R`.

The construction is also restricted to every ideal containing the regular
polynomial: under the quotient-to-remainder equivalence, the image of the ideal
is exactly its bounded coefficient module. This is the precise modern module
statement behind the source's passage from equations (22)--(23) to finitely
many `ξ` variables. It does not by itself identify the historical paired
`G₁/M₁` quotient or supply later-stage Smith data.

The module contains sixteen declarations (ten theorems and six definitions).
Its clean canonical receipt is
`artifacts/build/MathematicalCommons-Noether-PolynomialIdealsAndResultants1923-RegularQuotient-20260826T0548423174602-634afaa4.module.receipt.json`,
with 1,363,423,232 bytes observed peak and only `propext`,
`Classical.choice`, and `Quot.sound` in its axiom audits. The claim receipt is
`artifacts/build/claim-P22-regular-quotient-20260827T1748240448096-3aca3b68.json`.

`CommonTailQuotient.lean` closes that abstract paired-quotient step. For
submodules `M ≤ G` and a tail `T` disjoint from `G`, it proves
`(G ⊔ T)/(M ⊔ T) ≃ G/M` using Mathlib's
`LinearMap.quotientInfEquivSupQuotient`, and proves that every enlarged class
has a representative from `G`. The module's six declarations are deliberately
classified as source-facing `NEW_PACKAGING`, not new mathematics. Its clean
receipt is
`artifacts/build/MathematicalCommons-Noether-PolynomialIdealsAndResultants1923-CommonTailQuotient-20260827T2157043610703-850064d3.module.receipt.json`;
the observed peak was 1,132,634,112 bytes and the axiom audit again reports only
`propext`, `Classical.choice`, and `Quot.sound`. The claim receipt is
`artifacts/build/claim-P22-common-tail-quotient-20260827T2158428474453-64f62f7d.json`.

`RegularPairedQuotient.lean` then instantiates that abstract equivalence with
the actual bounded-part/principal-tail decomposition of a supplied regular
ideal pair `M ≤ G`. It identifies the paired quotient with the quotient of the
bounded coefficient modules, proves the former finite over the remaining-
variable polynomial ring, and transports a bounded representative to every
class. These six declarations are source-specific `NEW_PACKAGING`: they
assemble existing Mathlib finite-module APIs and the preceding local wrappers,
not new mathematics. The controlled claim stops at line 13160; line 13162's
ground-module characterization is promoted separately below. The clean module receipt is
`artifacts/build/MathematicalCommons-Noether-PolynomialIdealsAndResultants1923-RegularPairedQuotient-20260828T0057132656054-f5e829e8.module.receipt.json`,
with 1,387,941,888 bytes observed peak and the same three standard axioms. The
claim receipt is
`artifacts/build/claim-P22-regular-paired-quotient-20260828T0110324461242-014a6a7e.json`.

`FirstGroundPairedQuotient.lean` connects that supplied-pair package to the
actual source indexing. It proves `g₀` is the unit ideal exactly when the input
ideal is nonzero, represents source `g₁` by cutoff one in at least two total
variables, transports `I ≤ g₁` through `MvPolynomial.finSuccEquiv`, and obtains
the bounded quotient equivalence, module-finiteness, and bounded representatives
for this stage-one ideal quotient. Its eleven declarations are
`NEW_PACKAGING`. The clean receipt is
`artifacts/build/MathematicalCommons-Noether-PolynomialIdealsAndResultants1923-FirstGroundPairedQuotient-20260828T0156012692103-575448b6.module.receipt.json`,
with 1,348,321,280 bytes observed peak, empty stderr, and only `propext`,
`Classical.choice`, and `Quot.sound`. The claim receipt is
`artifacts/build/claim-P22-stage-one-ground-ideal-quotient-20260828T1412133846760-797a2f84.json`.

`FirstLinearFormModules.lean` closes the separate coordinate bridge. It models
the finite `ξ` coordinates and common `ζ` tail by
`Polynomial.degreeLT × principalTail`; regular division realizes the product by
addition. Under supplied regularity and membership hypotheses, the bounded,
tail, and full coordinate modules map to the bounded part, principal tail, and
actual containing ideal. The cutoff-one ground/original pair is then transported
through the coordinate quotient, actual ideal quotient, and bounded quotient in
one explicit chain. Its twenty declarations (eight theorems and twelve
definitions/abbreviations) are classified `FORMALIZED_GAP`. The module does not
claim named individual `ξᵢ`/`ζν` bases; line 13162's ground-module theorem is
promoted in the next module. Its
clean receipt is
`artifacts/build/MathematicalCommons-Noether-PolynomialIdealsAndResultants1923-FirstLinearFormModules-20260828T1458432494370-59aaa585.module.receipt.json`,
with 1,366,568,960 bytes observed peak, empty stderr, and only `propext`,
`Classical.choice`, and `Quot.sound`. The claim receipt is
`artifacts/build/claim-P22-first-linear-form-modules-20260828T1500160501084-3b7c5d91.json`.

`FirstGroundModule.lean` formalizes Definition I's formula (4) as
`nonzeroScalarSaturation` and proves its universal property: it is the least
ground module containing the supplied module. It then proves that a cutoff-one
source multiplier becomes exactly a nonzero scalar under
`MvPolynomial.finSuccEquiv`, in both directions. The resulting source theorem is
the exact equality
`boundedPartInDegreeLT (stageOneGroundIdeal I) k =
nonzeroScalarSaturation (boundedPartInDegreeLT (finSuccIdeal I) k)`, together
with the printed “all and only” membership form and Definition I's cancellation
criterion. These sixteen declarations are `FORMALIZED_GAP` and close line
13162; they do not silently assume regularity, a PID, or characteristic zero.
The clean receipt is
`artifacts/build/MathematicalCommons-Noether-PolynomialIdealsAndResultants1923-FirstGroundModule-20260828T1536217097235-72cee448.module.receipt.json`,
with 1,350,840,320 bytes observed peak, empty stderr, and only `propext`,
`Classical.choice`, and `Quot.sound`. The claim receipt is
`artifacts/build/claim-P22-first-ground-module-20260828T1620327764359-f0dc0f4c.json`
(4,560 bytes; SHA-256
`BE9D6549E7DB2F9E9D39AC0C154E0E7DB22E053E46F0611F13E29E96E18A8900`).

`FirstGroundModuleTorsion.lean` packages the decisive consequence for equation
(24). It proves `G/M` is torsion exactly when `G` lies in the nonzero-scalar
saturation of `M`; rank-nullity then gives equality of the relative
denominator's cardinal rank and `finrank` with the numerator. It also records
Satz I's same-rank theorem, proves the bounded stage-one module finite, and
specializes torsion and full rank to `G₁*/M₁*`. These ten declarations are
`FORMALIZED_GAP`. The clean receipt is
`artifacts/build/MathematicalCommons-Noether-PolynomialIdealsAndResultants1923-FirstGroundModuleTorsion-20260828T1611183796552-b3ea0d69.module.receipt.json`,
with 1,527,357,440 bytes observed peak, empty stderr, and the same three standard
axioms. This is the unlocalized full-rank premise; it does not pretend the
multivariate coefficient ring is a PID. The claim receipt is
`artifacts/build/claim-P22-first-ground-module-torsion-20260828T1620327764359-f0dc0f4c.json`
(4,542 bytes; SHA-256
`A76A3633431A1007696BBD68A4C39D0CE4A90306E3E65B0F133D3D23C1A67667`).

`FirstGroundModuleLocalization.lean` implements the localization immediately
before equation (24) with the source's variable boundary intact. Its tower is

```text
B = P[x₃,…],    A = B[x₂],    K = Frac(B),    R = K[x₂].
```

Thus only the later-variable coefficient ring `B` is inverted; the construction
never replaces `R` by `Frac(A)` and never makes `x₂` a unit. The module
identifies bounded polynomials with finite coefficient coordinates, proves that
nonzero-scalar saturation commutes with this coefficient localization, and
specializes that result to the actual cutoff-one ground/original pair. In
particular, it proves the localized ground module equals the saturation of the
localized original module and that the localized relative denominator has the
same `finrank` as its numerator. It does not add separately named localized
torsion or finite-generation endpoints.

These twenty-five declarations are `FORMALIZED_GAP`. The source is
`MathematicalCommons/Noether/PolynomialIdealsAndResultants1923/FirstGroundModuleLocalization.lean`
(21,883 bytes; SHA-256
`72806C7E6D5E982A86694A05402AA1D85CCDB7AA5D31E6CD7318AB7174696AB1`).
Its clean canonical build peaked at 1,408,970,752 bytes; the receipt is
`artifacts/build/MathematicalCommons-Noether-PolynomialIdealsAndResultants1923-FirstGroundModuleLocalization-20260828T1711488036548-b4e9f21a.module.receipt.json`
(7,321 bytes; SHA-256
`43BD1973BA6924D3B1E466BA3EDD16EF0AD257AC15A5880C6110C5FD28C262A0`).
The source-facing claim receipt is
`artifacts/build/claim-P22-first-ground-module-localization-20260828T1741336133599-43d2ef8c.json`
(5,041 bytes; SHA-256
`4A0F2C8C3BC83C43A856BB845D6674EFE7DBCBBB1DF569A2CFF6627EBA1255E0`).

`SmithPairedQuotient.lean` gives a deliberately generic equation-(24) scaffold.
For a supplied finite basis and full-rank relative denominator over a PID, it
exposes Mathlib's Smith numerator/denominator bases and diagonal coefficients,
decomposes the quotient into cyclic factors, composes this with common-tail
cancellation, and proves that the selected-basis transition determinant is the
product of those coefficients. These nine declarations (four theorems and five
definitions) are `NEW_PACKAGING`, not the historical localized `G₁*/M₁*`
instance and not a canonical divisibility-ordered elementary-divisor theorem.
The clean receipt is
`artifacts/build/MathematicalCommons-Noether-PolynomialIdealsAndResultants1923-SmithPairedQuotient-20260828T1459027809328-2d9a1f3c.module.receipt.json`,
with 1,342,902,272 bytes observed peak, empty stderr, and the same three standard
axioms. The claim receipt is
`artifacts/build/claim-P22-smith-paired-quotient-20260828T1500160501084-3b7c5d91.json`.

`FirstSmithPairedQuotient.lean` instantiates that scaffold for the actual
localized finite cutoff-one pair over
`R = Frac(P[x₃,…])[x₂]`. It selects a numerator basis `ηᵢ`, a relative-
denominator basis, and Smith coefficients `eᵢ`; proves the diagonal relation,
membership of `eᵢηᵢ` in the localized original module, and nonvanishing of
every `eᵢ`; identifies the finite relative quotient with the product of the
corresponding cyclic quotients; and proves that the selected-basis transition
determinant is `∏ i, eᵢ`. This is the finite source instance underlying
equation (24), not the whole displayed infinite system. It does not itself
assert a canonical divisibility ordering or construct the `ζ` tail; the
subsequent common-tail module supplies a freely adjoined identity-tail model.
It also does not identify the determinant product with Hentzelt's norm or
resultant, prove primitive normalization or choice independence, or construct
later stages.

These thirteen declarations are `FORMALIZED_GAP`. The source is
`MathematicalCommons/Noether/PolynomialIdealsAndResultants1923/FirstSmithPairedQuotient.lean`
(10,052 bytes; SHA-256
`14A628E4BA7F22C8DC729708309A5A7AA44E0BBF1E7076C6C108B442332ABC6D`).
Its clean canonical build peaked at 1,391,661,056 bytes; the receipt is
`artifacts/build/MathematicalCommons-Noether-PolynomialIdealsAndResultants1923-FirstSmithPairedQuotient-20260828T1726213885481-badb6014.module.receipt.json`
(7,276 bytes; SHA-256
`4DAF838C37B13AD66F7B0CB8367FD8A5E670BBB69B8D6D4EF0F2BE6B1854D32B`).
The source-facing claim receipt is
`artifacts/build/claim-P22-first-smith-paired-quotient-20260828T1741336133599-43d2ef8c.json`
(5,436 bytes; SHA-256
`336CF9B9535D87BE2D99C47CA94414141231E263F9D1BABE78BBA8231F4900A1`).

`FirstSmithCommonTail.lean` restores the independent `ζ` coordinates around
that actual localized finite pair. Four generic product-head quotient helpers
are `NEW_PACKAGING`: they compose Mathlib quotient equivalences and forget a
zero product coordinate. The other thirty-three declarations are
`FORMALIZED_GAP`. They embed `G₁*` and `M₁*` in

```text
G₁* × (τ →₀ R),    R = Frac(P[x₃,…])[x₂],
```

freely adjoin the same standard Finsupp basis to numerator and denominator,
prove the finite and tail summands disjoint, extend the selected Smith bases,
assign diagonal coefficient `1` to every tail coordinate, cancel the common
tail, and recover the actual finite cyclic-quotient decomposition. Taking
`τ = ℕ` gives the source-shaped countable sequence `ζ₀, ζ₁, …`. Every vector
has finite support, so the construction does not form an infinite determinant.

This is an explicit model of the printed independent tail, not yet a theorem
identifying it with a separately constructed and localized historical
unbounded `ζ`-module. The coefficient `1` records the identity action on the
shared tail; it is not a divisibility-order or canonical-normalization theorem.
The selected finite coefficients are still not proved divisibility ordered,
and determinant-norm/resultant identification, primitive normalization, choice
independence, and later stages remain open.

The module source is
`MathematicalCommons/Noether/PolynomialIdealsAndResultants1923/FirstSmithCommonTail.lean`
(25,766 bytes; SHA-256
`6A2AC9FC7F0550676DA302581E54FBC244DEC400D802E2415D190231A300245A`).
Its clean one-thread Lean 4.31 build exited zero with empty stderr, audited all
37 declarations, used only `propext`, `Classical.choice`, and `Quot.sound`, and
peaked at 1,421,987,840 bytes under the 2.5 GiB watcher. The receipt is
`artifacts/build/MathematicalCommons-Noether-PolynomialIdealsAndResultants1923-FirstSmithCommonTail-20260828T2012238968138-efd307ef.module.receipt.json`
(7,240 bytes; SHA-256
`9812CF23D7DFACC4E4D58AB573549C60255D0F2A2F85B021953E5067A211A6F9`).
The comprehensive claim receipt is
`artifacts/build/claim-P22-first-smith-common-tail-20260828T2016152269335-1092d717.json`
(7,422 bytes; SHA-256
`D2610B6B73598E372BCEE8FE6C8AC58E14763ABB9E43989928B0431C3860FAEF`).

`FirstSmithScalarQuotients.lean` makes the scalar quotient notation following
equation (24) precise. Fifteen generic declarations are `NEW_PACKAGING`: they
build a finite Smith filtration `D(s)`, characterize its coordinates, compute
colon ideals, and cancel a full common product tail. The other twenty
declarations are `FORMALIZED_GAP` instances for the actual localized cutoff-one
Smith pair and its arbitrary/countable freely adjoined common tail.

Here the historical slash is interpreted as the scalar colon ideal
`A.colon (B : Set E)`. For every selected finite coordinate, the one-step
formula

```text
M₁ / (M₁, ηᵢ) = (eᵢ)
```

is unconditional. In contrast, `D(s) / G₁` is exactly the infimum of the
principal ideals `(eⱼ)` over the coordinates not in `s`. It is simplified to
one distinguished `(eᵢ)` only when the theorem is supplied the explicit
hypothesis that every remaining `eⱼ` divides `eᵢ`. Neither Mathlib's selected
Smith coefficients nor this module supplies a canonical divisibility order.
The result also does not identify the determinant product with a norm or
resultant and does not identify the free common tail with the separately
constructed/localized historical unbounded tail.

The module source is
`MathematicalCommons/Noether/PolynomialIdealsAndResultants1923/FirstSmithScalarQuotients.lean`
(34,313 bytes; SHA-256
`D65B09A006E97F4B6F32FA50BC064BF401811069382CB2BA08DD5CB424BA7703`).
Its clean one-thread Lean 4.31 build exited zero with empty stderr, audited all
35 declarations, used only `propext`, `Classical.choice`, and `Quot.sound`, and
peaked at 1,462,034,432 bytes under the 2.5 GiB watcher. The receipt is
`artifacts/build/MathematicalCommons-Noether-PolynomialIdealsAndResultants1923-FirstSmithScalarQuotients-20260828T2052403988381-386b0cec.module.receipt.json`
(7,285 bytes; SHA-256
`75EA954635F63B2A23AEC4CF866701006CEFA3A14F4FED37816A724EFB4D4593`).
The comprehensive claim receipt is
`artifacts/build/claim-P22-first-smith-scalar-quotients-20260828T2055573367899-6e27c54b.json`
(7,537 bytes; SHA-256
`681152AA43FCB326269455A7C38398DC34EF2B5F01A03967C4C8F14B2440A022`).

`FirstSmithGroundReciprocity.lean` advances Satz II and equation (5), lines
12815--12844. It first types Definition II's module-valued quotient `M / J`
separately from the ideal-valued scalar colon `M.colon G`. For a principal
ideal `(e)`, the former is the preimage of `M` under multiplication by `e`.
Six generic declarations providing this operation, its saturation theorem, and
the diagonal reciprocal calculation are `NEW_PACKAGING`. Two declarations are
`FORMALIZED_GAP` instances for the actual localized cutoff-one ground/original
pair.

Under the explicit hypothesis that every selected Smith coefficient divides
the distinguished `eᵢ`, the module proves the two reciprocal source formulas

```text
M₁* / G₁* = (eᵢ),       G₁* = M₁* / (eᵢ).
```

The first slash is a scalar colon ideal; the second is a module-valued ideal
quotient. The second equality uses the already proved source identity that
`G₁*` is exactly the nonzero-scalar saturation of `M₁*`. Mathlib's selected
Smith coefficients are still not proved divisibility ordered, so the theorem
does not silently identify `i` with a canonical historical `ρ`.

The module source is
`MathematicalCommons/Noether/PolynomialIdealsAndResultants1923/FirstSmithGroundReciprocity.lean`
(9,122 bytes; SHA-256
`B34074BD5D298D53470B576CD322A3E1C44D7FC265B10480D35E95F213A52A07`).
Its clean one-thread Lean 4.31 build exited zero with empty stderr, audited all
eight declarations, used only `propext`, `Classical.choice`, and `Quot.sound`,
and peaked at 1,380,622,336 bytes under the 2.5 GiB watcher. The receipt is
`artifacts/build/MathematicalCommons-Noether-PolynomialIdealsAndResultants1923-FirstSmithGroundReciprocity-20260828T2217329496419-78b62eaf.module.receipt.json`
(7,301 bytes; SHA-256
`D1D61114AC63068550FB3B51EF4DE1C44BC3B02F0967F50D147BFCF96D4B16C9`).
The comprehensive claim receipt is
`artifacts/build/claim-P22-first-smith-ground-reciprocity-20260828T2221155880785-bb27cb08.json`
(6,776 bytes; SHA-256
`C7648327017131D30B5801A09F4E08F0F3E5A07C3FD7F6B4E70399607781A6A0`).

`FirstSmithAnnihilatorBounds.lean` advances the opening algebraic step of Satz
VIII, lines 13340--13342, using the actual finite localized equation-(24)
Smith quotient. Ten generic `NEW_PACKAGING` declarations compute annihilators
of products of cyclic quotients and prove finite ideal-product bounds. Six
`FORMALIZED_GAP` declarations instantiate those results for the cutoff-one
pair over `Frac(P[x₃,…])[x₂]`.

The construction deliberately replaces the unavailable ordered “greatest
elementary divisor” by the intrinsic annihilator
`A = Ann(G₁*/M₁*) = ⋂ᵢ (eᵢ)`. With `D = ∏ᵢ eᵢ`, it proves `(D) ≤ A` and
`A^ρ ≤ (D)`, the generator divisibilities `a ∣ D` and `D ∣ a^ρ`, and equality
of the radicals of `(D)` and `A`. It also identifies `A` with the scalar colon
of the actual relative denominator by the whole localized ground carrier.
No theorem calls `D` the historical resultant form or calls `a` a normalized
historical elementary-divisor form.

The module source is
`MathematicalCommons/Noether/PolynomialIdealsAndResultants1923/FirstSmithAnnihilatorBounds.lean`
(14,013 bytes; SHA-256
`417314B11EE176E90D365FA706EE01B0F48A6BB0A05293A88339CCF693880292`).
Its clean one-thread Lean 4.31 build exited zero with empty stderr, audited all
16 declarations, used only `propext`, `Classical.choice`, and `Quot.sound`, and
peaked at 1,402,142,720 bytes under the 2.5 GiB watcher. The receipt is
`artifacts/build/MathematicalCommons-Noether-PolynomialIdealsAndResultants1923-FirstSmithAnnihilatorBounds-20260828T2245349715763-862933b6.module.receipt.json`
(7,303 bytes; SHA-256
`40BE879598DEAFCEDA0C9BBC8B8FD8437E46062F0D0C164E7B01F0002C52CC37`).
The comprehensive claim receipt is
`artifacts/build/claim-P22-first-smith-annihilator-bounds-20260828T2248235911582-32a08ca0.json`
(6,826 bytes; SHA-256
`E39F795AE5CD93B03FA7F29182AB70C347B77E3E59DE424E1B9B6C94E2682421`).

`FirstSmithGreatestCoefficientBridge.lean` connects the intrinsic annihilator
bounds back to Hentzelt's displayed greatest elementary divisor, but only under
the explicit `IsGreatestRemainingDivisor` hypothesis. Its four generic
`NEW_PACKAGING` theorems prove that the coefficient ideal is `(eᵢ)`, that
`eᵢ ∣ ∏ⱼeⱼ`, that `∏ⱼeⱼ ∣ eᵢ^ρ`, and that the generated ideals have the
same radical and field-valued vanishing behavior. Four `FORMALIZED_GAP`
theorems instantiate this bridge for the actual localized cutoff-one pair and
join the Satz-II reciprocal identities to the opening of Satz VIII.

The module does not prove existence of a greatest selected coefficient,
canonical ordering or normalization, choice independence, descent from the
coefficient localization, identification with primitive `R^(2)` or `E^(2)`, or
any later stage. Its source is
`MathematicalCommons/Noether/PolynomialIdealsAndResultants1923/FirstSmithGreatestCoefficientBridge.lean`
(10,807 bytes; SHA-256
`1F9626ECC4B8616BCE75CA9BD1BC988ADB597767F49D8FDD74AFDDC677E2BDCB`).
The clean one-thread Lean 4.31 build exited zero with empty stderr, audited all
eight theorems, used only `propext`, `Classical.choice`, and `Quot.sound`, and
peaked at 1,368,829,952 bytes under the 2.5 GiB watcher. Its receipt is
`artifacts/build/MathematicalCommons-Noether-PolynomialIdealsAndResultants1923-FirstSmithGreatestCoefficientBridge-20260828T2331335689853-381370ff.module.receipt.json`
(7,375 bytes; SHA-256
`9ACF33D84DE5D7EA2E960B84699F003AA6DA17C67ACCB208D4A996662DAFE05E`).

`SatzVIIIOneStageDescent.lean` formalizes equation (33), lines 13344--13373,
as one denominator-descent step. Four generic `NEW_PACKAGING` theorems take
elementwise multiplier witnesses on a finite ideal basis and construct one
allowed multiplier that works on its span. The source-shaped definition and
five `FORMALIZED_GAP` theorems express the equation-(33) witness, place
`E * G` in the next ground ideal, uniformize the multiplier automatically from
Noetherian finite generation, and specialize the result to the first stage.

This is deliberately conditional on the supplied integral polynomial `E` and
the elementwise equation-(33) witnesses. It does not derive them from the
integral lift or localized Smith data, construct or normalize historical
`E^(i)`, identify a determinant product with `R^(i)`, iterate lines
13374--13380, or prove equation (34). The module source is
`MathematicalCommons/Noether/PolynomialIdealsAndResultants1923/SatzVIIIOneStageDescent.lean`
(9,291 bytes; SHA-256
`53F41EF053C80CAA3C8BE851C760C4995401E8AFBEB68D6CDB9F38548D49135C`).
Its clean one-thread Lean 4.31 build exited zero with empty stderr, audited all
ten declarations (one definition and nine theorems), used only `propext`,
`Classical.choice`, and `Quot.sound`, and peaked at 1,335,193,600 bytes under
the 2.5 GiB watcher. Its receipt is
`artifacts/build/MathematicalCommons-Noether-PolynomialIdealsAndResultants1923-SatzVIIIOneStageDescent-20260828T2334520752660-df4abd76.module.receipt.json`
(7,265 bytes; SHA-256
`095DFFBAA66EAE1CA7AE878B66B4FA87C7A93CA23C0E3B34C567238DD712DAB7`).

`FirstSmithIntegralNumerator.lean` clears the first localization barrier in
lines 13323--13349. Two generic `NEW_PACKAGING` theorems clear localized
submodule membership by an integral denominator. Two `FORMALIZED_GAP`
theorems apply that mechanism to the actual cutoff-one Smith pair: under the
explicit greatest-remaining-divisor hypothesis, the selected localized Smith
coefficient acts on the localized ground module, and it has a nonzero integral
numerator `a` whose action on every bounded ground vector can be returned to
the bounded original module after multiplication by a genuine later-variable
denominator.

This is the strongest honest integral statement currently available. It does
not transport the bounded action to every element of the full stage ground
ideal, prove `HasEquation33Witness`, normalize `a` to a primitive historical
`E^(2)`, or prove choice independence. The module source is
`MathematicalCommons/Noether/PolynomialIdealsAndResultants1923/FirstSmithIntegralNumerator.lean`
(9,458 bytes; SHA-256
`ECA6FBF7CAA909D689F6369B143E3969553D9004C335E6FA1C2F316DB70E328F`).
Its clean one-thread Lean 4.31 build exited zero with empty stderr, audited all
four theorems, and peaked at 1,383,194,624 bytes under the 2.5 GiB watcher.
Its receipt is
`artifacts/build/MathematicalCommons-Noether-PolynomialIdealsAndResultants1923-FirstSmithIntegralNumerator-20260829T1518064363393-bf431c1b.module.receipt.json`
(7,300 bytes; SHA-256
`4717412B681D6226D9049DDAEA9C173A86878134C0FEFE87D7BB5FB38FE0327E`).

`SatzVIIIEquation33Iteration.lean` proves the finite induction in lines
13344--13380 once the equation-(33) witnesses are supplied. Its two generic
`NEW_PACKAGING` declarations give the ideal-inclusion interface and reusable
finite-window iteration; four `FORMALIZED_GAP` declarations prove the terminal
identity `g_n = I`, the printed prefix induction, the conditional `E`-product
half of equation (34), and the terminal tail-window conclusion.

The module does not construct the witness family, identify its forms with
primitive or canonical historical `E^(i)`, prove the parallel `R^(i)` product,
or establish determinant-norm/resultant identities. Its source is
`MathematicalCommons/Noether/PolynomialIdealsAndResultants1923/SatzVIIIEquation33Iteration.lean`
(6,799 bytes; SHA-256
`A1DEDECBA8D6945B719A0014C9D46579DCC6AFC589B2DADB7B990E84405EE128`).
Its clean one-thread Lean 4.31 build exited zero with empty stderr, audited all
six theorems, and peaked at 1,339,314,176 bytes under the 2.5 GiB watcher. Its
receipt is
`artifacts/build/MathematicalCommons-Noether-PolynomialIdealsAndResultants1923-SatzVIIIEquation33Iteration-20260829T1519573911099-a856eb8a.module.receipt.json`
(7,301 bytes; SHA-256
`953FA6666354A4285223B06D5D43F3C32DB85DCAB01788312B15E11580735544`).

`FirstSmithEquation33Bridge.lean` closes the bounded-to-full transport at the
first actual stage. Its fourteen declarations rebuild a bounded
second-variable coordinate in the original multivariate ring, prove exact
compatibility with integral scalar multiplication, and use regular division
by the supplied regular `C ∈ I` to represent every member of
`stageGroundIdeal 1 I` modulo the original ideal. A denominator from the
genuinely later coefficient ring lifts to a nonzero polynomial free of the
first two original variables, exactly the cutoff-two multiplier required by
equation (33).

Consequently, under the same explicit greatest-selected-coefficient hypothesis
as the preceding Smith bridge, the final theorem retains the localization
clearing equality, returns a nonzero integral numerator and nonzero full-ring
lift, and proves `HasEquation33Witness I 1` for that lift. This first-stage
form is not asserted to be primitive, normalized, canonical, or independent
of the Smith choices. The module does not construct later Smith stages or the
parallel `R^(i)` resultant product. Its source is
`MathematicalCommons/Noether/PolynomialIdealsAndResultants1923/FirstSmithEquation33Bridge.lean`
(17,378 bytes; SHA-256
`876DB09F6858D2237C6730ED823A2721C09F0D854EDA8DE31FA9A925B05210BE`).
Its clean one-thread Lean 4.31 build exited zero with empty stderr, audited all
fourteen declarations, and peaked at 1,393,115,136 bytes under the 2.5 GiB
watcher. Its receipt is
`artifacts/build/MathematicalCommons-Noether-PolynomialIdealsAndResultants1923-FirstSmithEquation33Bridge-20260829T1549364931065-c50c17d9.module.receipt.json`
(7,294 bytes; SHA-256
`722B7DB06B9E0664F155B9559839EC5AF719C7E6089D8367EE5018557D8AD907`).
The cluster claim path is
`artifacts/build/claim-P22-first-smith-equation33-full-20260829T1552050773212-64de772d.json`.

`FirstSmithCoefficientProductNumerator.lean` advances the same cutoff without
silently identifying the selected Smith product with the historical resultant.
Its four `NEW_PACKAGING` theorems prove that an equation-(33) witness survives
right multiplication, clear a localized divisibility into a compatible
integral numerator multiple, prove the finite selected-Smith-coefficient
product nonzero, and apply those facts to the actual cutoff-one Smith data.
Under the existing regular-member and explicit greatest-selected-coefficient
hypotheses, the final theorem returns nonzero integral numerators `a` and `r`,
proves `a ∣ r`, retains both localization-clearing equations, and gives
`HasEquation33Witness I 1` for both full-ring lifts.

The local zero-based cutoff `1` is the source's stage `i = 2`. The numerator
`r` is an integral numerator for the finite selected-coefficient product; it is
not identified with historical `R^(2)`, a historical resultant, a primitive or
normalized form, a canonical choice, or an object independent of the selected
Smith/localization data. Its source is
`MathematicalCommons/Noether/PolynomialIdealsAndResultants1923/FirstSmithCoefficientProductNumerator.lean`
(9,279 bytes; SHA-256
`C7E8C66C46A88FC578A040A60A9CD6B8FC6661D3965AD03A2AA696420AE77362`).
The clean one-thread Lean 4.31 build exited zero with empty stderr, audited all
four declarations, and peaked at 1,421,578,240 bytes under the 2.5 GiB watcher.
Its receipt is
`artifacts/build/MathematicalCommons-Noether-PolynomialIdealsAndResultants1923-FirstSmithCoefficientProductNumerator-20260829T1607180026573-04e54684.module.receipt.json`
(7,390 bytes; SHA-256
`1A73C7CC2BC2E601E7B938801D8C4153791216B39C724F4309356E6BC2F00AE9`).

`FirstSmithPrimitiveCoefficientProductForm.lean` advances the selected
cutoff-one proxies through the primitive-form step in source lines
13323--13350. Two generic `NEW_PACKAGING` declarations show that a permitted
late-variable factor can be absorbed into an equation-(33) multiplier and that
a nonzero polynomial becomes associated with its primitive part after mapping
the coefficient domain to its fraction field. Two
`FORMALIZED_SOURCE_PACKAGING` declarations apply those facts to the actual
conditional cutoff-one package.

Under a regular `C ∈ I` and an explicitly selected greatest Smith coefficient,
the final theorem returns primitive nonzero integral representatives `e` and
`r`, with nonzero full-ring lifts. Their localized images are associated with
the selected Smith coefficient and the finite selected-coefficient product;
in the integral polynomial ring they satisfy
`e ∣ r` and `r ∣ e ^ localizedSecondVariableSmithRank`, the latter obtained by
primitive Gauss descent. Both full-ring lifts retain
`HasEquation33Witness I 1`. Local cutoff `1` is again source stage `i = 2`.

These are selected proxies only. They are not identified with the historical
`E^(2)` or `R^(2)`, a module norm, the gcd of maximal minors, or a historical
resultant. The companion transition-determinant module below supplies only a
selected-basis determinant/product equality and basis-change association. The
theorem does not establish a
canonical normalization, independence of the selected Smith/localization
data, existence of a greatest index, or any later-stage form or witness. Its
controlled witness is `NOETH-DE-ED-0014`, SHA-256
`EE226847656BC4D65EDDA9E9BF9BB1D25797C0C6D672D267D94A97FD88C7AD58`.
The source is
`MathematicalCommons/Noether/PolynomialIdealsAndResultants1923/FirstSmithPrimitiveCoefficientProductForm.lean`
(12,041 bytes; SHA-256
`0DB8944E6447B3678CDF56959FC5552832DE62691A8B02B4E35CBAC133B1F06E`).
The clean one-thread Lean 4.31 build exited zero, produced empty stderr, printed
clean axiom audits for all four declarations, and peaked at 1,412,005,888 bytes
under the 2.5 GiB watcher. Its 805-byte stdout has SHA-256
`8A1B6E45CFBAC830A36068ECA989E33DF96F69BC3F38DFB2A42636676B8139F7`;
the 510,640-byte `.olean` has SHA-256
`E3302DDFE1614A0D3E8DA5973694F3E969AA4D4176E38029D6143BDCE75E7242`.
The receipt is
`artifacts/build/MathematicalCommons-Noether-PolynomialIdealsAndResultants1923-FirstSmithPrimitiveCoefficientProductForm-20260829T1922416820685-b3774a59.module.receipt.json`
(7,428 bytes; SHA-256
`BD80AB6E88E4200DB203B392C38F0942BD2CE56A913B7B05ABE2099F10B3EAC7`).

`FirstSmithPrimitiveTransitionDeterminantForm.lean` records the determinant edge
at controlled source lines 13323--13327. It defines the determinant of a chosen
localized ground-to-denominator linear equivalence, proves that the selected
Smith-basis determinant is exactly the finite selected-coefficient product, and
proves that any other such equivalence gives an associated determinant. Its
source-facing five-declaration theorem then associates the primitive product
proxy with that selected determinant after localization. This is selected-basis
packaging only: it does not identify the object with historical `R^(2)`,
Hentzelt's module norm, a gcd of maximal minors, a resultant, or a
canonical/choice-independent form. The source is
`MathematicalCommons/Noether/PolynomialIdealsAndResultants1923/FirstSmithPrimitiveTransitionDeterminantForm.lean`
(12,260 bytes; SHA-256
`D7E1454B7D1175DF7B68FC150A81D16CE8FA762C7B0A9BAEC706156FD0CC3579`). The
clean one-thread Lean 4.31 build exited zero with empty stderr, audited all five
declarations, and peaked at 1,428,381,696 bytes under the 2.5 GiB watcher. Its
receipt is
`artifacts/build/MathematicalCommons-Noether-PolynomialIdealsAndResultants1923-FirstSmithPrimitiveTransitionDeterminantForm-20260829T2024252306168-af0bed92.module.receipt.json`
(7,456 bytes; SHA-256
`70551DBCF893AC7384F6F4A223A8BE4944A11BA05FE32A862130B9486942D922`); the
audited `.olean` is 342,760 bytes with SHA-256
`F03035E1595AD9A6FD6C8BF7D1C422CC55800A094FCCB957E4B32AD6C31CF06B`.

`DeterminantalIdealScaffold.lean` supplies the next infrastructure layer without
overstating the source. Its ten `NEW_PACKAGING` declarations define a selected
`k`-minor as a submatrix determinant and the corresponding ideal as the span of
all selected minors. It proves generator membership, repeated-row and repeated-
column vanishing, the all-zero-minors bottom criterion, the positive-degree zero-
matrix bottom case, and the degree-zero top case. This is source-neutral finite-
matrix vocabulary: it does not prove Cauchy--Binet or exterior-power coefficient
invariance, construct a Fitting ideal or maximal-minor gcd, or identify any
object with Hentzelt's module norm, historical `R^(2)`, a resultant, or a
canonical/choice-independent form. The 6,009-byte source has SHA-256
`1BCAAE22D0B4E18243A4F575DC2DBE2A9DE7F1FAF65783D524B179F379F63B80`.
Its clean one-thread Lean 4.31 build audited all ten declarations, produced empty
stderr, and peaked at 1,167,695,872 bytes. The receipt is
`artifacts/build/MathematicalCommons-Noether-PolynomialIdealsAndResultants1923-DeterminantalIdealScaffold-20260829T2119094849183-578e0ed0.module.receipt.json`
(7,291 bytes; SHA-256
`F99EEE43D3FE34045D5582AB83F394158EBE9D0B09787799BE8100DC332087B3`);
the 82,336-byte `.olean` has SHA-256
`EDACBAFCB7C32A3AC15440600E2C2DD85B8D51039EBB199E096FE2392E4D576B`.
The associated claim receipt is
`artifacts/build/claim-P22-determinantal-ideal-scaffold-20260829T2119094849183-578e0ed0.json`.

P22 now has 576 canonical declarations across the base and thirty-eight support
modules. The integrated local graph contains 53 direct Noether imports and 55
current targets including both umbrellas. The new sealed graph checkpoint is
`artifacts/build/module-graph-checkpoint-20260829T2141556003305-de54d554.json`
(3,512 bytes; SHA-256
`BE88D5C55C607A7F9B7B9DFA4F3543C76F91F73550F52124A54E7D521377BA4A`). It
chains the preceding 54-target checkpoint and keeps the checkpoint-chain maximum
at 1,922,387,968 bytes under the 3 GiB worker envelope. The fresh Noether
umbrella receipt is
`artifacts/build/MathematicalCommons-Noether-20260829T2122201733912-236d52be.module.receipt.json`
(6,730 bytes; SHA-256
`814C126E414953A59DB9302E943FD8F3772DFABA4AEE6BD3CCEF309A0957A0A1`;
peak 1,919,422,464 bytes), and the fresh full-umbrella receipt is
`artifacts/build/MathematicalCommons-20260829T2141556987939-211968ff.module.receipt.json`
(6,650 bytes; SHA-256
`ECC8A36F324FCE75310109465DE8092BF7239B19C3CB223A32884D0F1F5497E9`;
peak 1,918,066,688 bytes). The prior transition-determinant claim remains
retained, and the scaffold claim records the new cluster. The prior 54-target
checkpoint remains retained as the preceding graph
pin, rather than being rewritten.

For the preceding localization/finite-Smith checkpoint, an independent
read-only pin, receipt, axiom, import-graph, ledger, and controlled-source
recheck is retained as
`artifacts/build/evidence-audit-P22-localization-smith-20260828T1758017380965-820e28e2.json`
(3,345 bytes; SHA-256
`9C897A87FAD9572D868E4E2553E7410845629584A1018B39FAFC8D297D2E0BAA`).

## Canon and scope constraints

- P18's resultant layout is primary-witness verified and P22 confirms its
  staged/triangular meaning. It is not a transcription correction.
- Historical module and ideal divisibility run opposite to modern inclusion;
  every Lean statement must state its orientation explicitly.
- `N(G | M)` is a determinant of a transition between finite module models.
  It must not be replaced silently by `Algebra.norm` without an equivalence
  proving that identification.
- “Primitive” and “regular in `x_i`” include normalization and coefficient
  localization choices; equality of resultants is generally only meaningful
  after those choices are fixed.
- Equation (12) is a full lower-unitriangular coordinate matrix with one
  independent parameter `u_{μν}` for every `ν < μ`. An elementary shear is
  useful implementation substrate but is not itself the printed transform.
- Canon-QA item `NOETH-QA-034` remains open for line 13319, where the printed
  footnote appears to place identical formulas on both sides of “not
  isomorphic.” The missing distinction is not securely recoverable, so no
  correction is asserted and no German or translation file was edited.

## Formalization route

The source-faithful coefficient localization and the selected finite Smith
instance for the actual cutoff-one pair are complete. The remaining route is:

1. Identify the freely adjoined countable Finsupp `ζ` tail with a separately
   constructed and source-localized historical unbounded module, and strengthen
   the selected finite Smith coefficients to the intended divisibility-ordered
   presentation where the available PID infrastructure permits it. The current
   coefficient-`1` theorem is identity-tail data; no infinite determinant is
   intended or asserted.
2. Identify the selected-basis determinant product with Hentzelt's determinant
   norm and first-stage resultant, including historical/canonical
   primitive-form identification and independence from the finite bases and
   regular-polynomial choices.
3. Iterate the completed finite specialized coordinate construction through
   later ground ideals to produce the successive `C^(i)`, `G_i/M_i`, Smith data,
   and primitive normalizations of `R^(i)`.
4. Extend the completed cutoff-one equation-(33) witness to the later ground
   ideals as their successive regular modules and Smith data become available,
   and normalize the resulting `E^(i)`. The finite iteration is already
   complete for a supplied witness family; combine a fully constructed family
   with the parallel `R^(i)` product, determinant-norm/resultant identification,
   and historical primitive-form identification to finish equation (34).
5. Build the successive determinantal ideals and strengthen the promoted
   finite-coordinate substrate and Nullstellensatz corollary to Satz XII's
   finite compatible-zero construction.
6. Only then state the unique
   compatible-zero and multiplicity results of Satz XII--XIII.
