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
| 12752, Definition I | ground module: no proper divisor of equal rank | `Submodule`; `Module.rank`; Smith-normal-form infrastructure | The historical divisor convention and saturation-like construction need a source-shaped definition. |
| 12763--12795, Satz I | unique smallest ground-module divisor of equal rank | `Submodule.exists_smith_normal_form_of_rank_eq` | Smith bases are strong substrate, but no pinned theorem packages Hentzelt's ground module with this universal property. |
| 12800--12810, Definition II | scalar quotient of two linear-form modules | `Submodule.colon`; `Submodule.mem_colon` | Modern colon ideals model the condition; the source orientation must be made explicit. |
| 12815--12844, Satz II | reciprocal relation with the highest elementary divisor | `Submodule.smithNormalFormCoeffs`; `Ideal.smithCoeffs` | Smith coefficients exist, but the precise ground-module quotient identities are not packaged. |
| 12849--12895, Satz III | quotient representation over a polynomial/domain coefficient ring | localization and fraction-field APIs | The generalized statement is a gap; it cannot be inferred merely from PID Smith form. |
| 12906--12918, Definition III | norm as determinant of the transition from ground module to module | `LinearMap.det`; `Algebra.norm_eq_matrix_det`; Smith bases | Modern determinant norms give the right language after finite-free hypotheses are reconstructed. |
| 12919--12922, Satz IV | equal norm plus divisibility and equal rank imply module equality | determinant and Smith-normal-form APIs | No exact pinned declaration was found; equality of determinants alone is insufficient without the source's divisibility structure. |
| 12924--12998, Satz V | coprime factorization of a norm gives unique module factors | `IsCoprime`; Chinese-remainder and Smith infrastructure | The source-specific module reconstruction is missing. |
| 13004--13037, equation (12) and Definition IV | transformed ideals under the full lower-unitriangular generic coordinate matrix `U` | `MvPolynomial.bind₁`; algebra equivalences; homogeneous components; algebraic independence; ideal maps | The full family `y_μ = x_μ + Σ_{ν<μ} u_{μν}x_ν`, its recursive inverse, ideal transport, exact total-degree preservation, generic leading-coefficient nonvanishing, and existence of a regular member in every nonzero transformed ideal are promoted. Characteristic-zero descent to an actual finite ground-field lower-unitriangular equivalence is also promoted. The successive later-stage regular elements remain. |
| 13046--13055, Definition V | successive ground ideals | localization extension/contraction; local `groundIdealAlong` | The literal submonoid of nonzero polynomials free of the earlier variables, its source/zero-based indexing dictionary, equation-(16) membership, and stage antitonicity are promoted. |
| 13057--13107, Satz VI | ground ideals of transformed ideals are transformed | relative Dedekind--Mertens; bounded Kronecker substitution; parameter localization | Equation (17), simultaneous common-denominator presentations, coefficient reconstruction, late-variable preservation, and the final two-sided transformed-contraction equality are promoted with no primary or saturation hypothesis. |
| 13123--13319, Satz VII; equations (21)--(23) at 13134--13160 | infinite monomial module reduces to a finite module; only finitely many elementary divisors are nonunits | finite-free, Smith-normal-form, monic polynomial division, submodule sums, and polynomial-evaluation APIs | Equations (21)--(23) are promoted for a supplied degree-`k` polynomial regular in `x₁`: exact bounded representatives, their `Fin k` coefficient vectors, the internal decomposition of every containing ideal into its bounded part and disjoint principal tail, the finite free quotient, and the paired common-tail quotient equivalence. Equation (12) constructs and finitely specializes the first regular member for every nonzero ideal while preserving any supplied finite family of witnesses. Iteration through later variables, determinant data, the nonunit elementary-divisor theorem, and auxiliary-choice independence remain open. |
| 13153--13160, equation (23) | isomorphism of residue-class systems after adjoining the same independent tail | `LinearMap.quotientInfEquivSupQuotient`; quotient modules; `LinearEquiv` | The concrete abstract equivalence and representative existence theorem are packaged with historical divisibility oriented explicitly as denominator `M ≤ G`. This is `NEW_PACKAGING` of Mathlib's second isomorphism theorem. |
| 13323--13335, Definition VI | stage resultants, elementary-divisor forms, and their products | `associated_norm_prod_smith`; `Ideal.smithCoeffs`; `Matrix.det` | Mathlib relates a finite-free norm to Smith coefficients, but Hentzelt's staged modules and primitive normalizations still need construction. |
| 13340--13382, Satz VIII | `E_m ∣ R_m`, `R_m ∣ E_m^N`, and tail products annihilate ground ideals modulo `m` | ideal radicals, divisibility, evaluation | The divisibilities themselves remain a gap. Their radical and zero-set consequence is now formally packaged. |
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

P22 now has 305 canonical declarations across the base and seventeen support
modules, and its ledger has 31 claim/definition records.

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
- No new German discrepancy was found in this exact-range audit. No German or
  translation file was edited.

## Formalization route

1. Iterate the completed finite specialized coordinate construction through
   the later ground ideals to produce the source's successive `C^(i)`. Generic
   coefficient nonvanishing, exact degree preservation, ideal-level existence,
   simultaneous finite specialization, and regular-polynomial division are
   already promoted.
2. Instantiate the promoted regular quotient, exact bounded-ideal-image
   equivalence, and abstract common-tail quotient at every historical
   `G_i/M_i` stage; then define its Smith coefficients, determinant norm, and
   the primitive normalization of `R^(i)`.
3. Prove Satz VIII's divisibilities, discharging the hypotheses of the promoted
   radical/zero-set bridge.
4. Build the successive determinantal ideals and strengthen the promoted
   finite-coordinate substrate and Nullstellensatz corollary to Satz XII's
   finite compatible-zero construction.
5. Only then state the unique
   compatible-zero and multiplicity results of Satz XII--XIII.
