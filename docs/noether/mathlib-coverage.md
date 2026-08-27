# Emmy Noether: Mathlib coverage audit

This is a declaration-level living audit, not yet a complete theorem inventory
of all 43 works. The paper-level queue is indexed in
[paper-inventory.md](paper-inventory.md). Results below were checked against
the pinned Mathlib `v4.31.0` source tree at resolved revision
`fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`.

## *Der Endlichkeitssatz der Invarianten endlicher Gruppen* (1916)

| Source item | Mathlib declaration | Coverage | Local declaration / state |
|---|---|---|---|
| Lines 5871–5888, one-element specialization of the Galois resolvent | `MulSemiringAction.charpoly` and its `charpoly_eq`, `monic_charpoly`, `eval_charpoly`, `smul_charpoly`, `smul_coeff_charpoly` lemmas | `MATHLIB_EXACT` for this specialization | `orbitPolynomial_audit_bundle`; green source-linked packaging |
| Line 5888, multivariate resolvent coefficients form a finite full invariant system | orbit polynomial is only a partial ingredient | `GAP_CANDIDATE` | not yet formalized |
| Lines 5931–5933, power-sum full system and degree bound by the group order | symmetric-polynomial infrastructure exists, but no end-to-end result was found | `GAP_CANDIDATE` | dependency design in progress |

The local orbit-polynomial module is deliberately not advertised as the 1916
finite-generation theorem. Noether's product uses `z +` a transformed linear
form; Mathlib's `X - C (g • x)` agrees after negating that linear form. The
multivariate coefficient extraction, generation proof, coefficient-ring
assumptions, and nonmodular degree bound remain open.

## *Invariante Variationsprobleme* (1918)

The controlled packet has exactly two author-labelled theorems: Satz I at line
8604 and Satz II at line 8606. The “Hilbertsche Behauptung” is a derived iff at
line 9029, after the definition of improper currents at line 9027; its
translation/energy specialization is at line 9049.

| Source item | Mathlib coverage | State |
|---|---|---|
| Test-function separation used at lines 8714–8720 | `ae_eq_zero_of_integral_contDiff_smul_eq_zero` gives a.e. zero; `Measure.eq_of_ae_eq` upgrades continuous functions pointwise | local `continuous_eq_zero_of_integral_contDiff_smul_eq_zero`, `NEW_PACKAGING`; green bounded build |
| Satz I forward: finite continuous symmetry gives divergence relations | no end-to-end theorem found | `DEFERRED_INFRASTRUCTURE` |
| Satz I converse | source qualifications at lines 8732–8744; no sufficient group-integration infrastructure | `BLOCKED_SOURCE` until explicitly restated |
| Satz II forward: arbitrary-function symmetry gives differential identities | test-function and integration components exist; jets/Euler operator/formal adjoints do not | `DEFERRED_INFRASTRUCTURE` |
| Satz II converse | source qualifications at lines 8829–8843; no gauge-pseudogroup integration theorem | `BLOCKED_SOURCE` until explicitly restated |
| Hilbert improper-current iff | no quotient of currents by trivial/Euler–Lagrange terms found | `DEFERRED_INFRASTRUCTURE` |

Useful existing anchors include integration by parts, a box divergence theorem,
parameter differentiation under the integral, derivative-zero constancy,
`LieGroup`, `ContMDiffSMul`, and manifold integral-curve existence. They do not
substitute for the missing finite-jet, prolongation, total-derivative,
Lagrangian/Euler, formal-adjoint, generalized-symmetry, or conservation-law
quotient layers.

The source assumes sufficient differentiability, invertible transformations,
essential parameters/functions, arbitrary boundary-vanishing variations, and
excludes trivial infinitesimal transformations. Its converse proofs also carry
division and group-closure caveats. The ledger therefore refuses an
unqualified modern iff.

## *Die Endlichkeit des Systems der ganzzahligen Invarianten binärer Formen* (1919)

The main result at lines 9303–9305 is finite generation over the integers, not
merely finite generation over a field. The raw coefficient convention at line
9397 must be preserved in a formal polynomial action.

| Source item | Mathlib coverage | State |
|---|---|---|
| Main finite generation for integral relative invariants, lines 9303–9305 and 9513–9515 | abstract fixed-ring integrality and Artin–Tate exist | `GAP_CANDIDATE`; arithmetic and binary-form specialization missing |
| Satz I, bracket generation, line 9320 and conclusion 9836 | determinant/polynomial primitives only | high-value `GAP_CANDIDATE` |
| Satz II, quotient-closed monomial systems, lines 9322–9330 | `Submonoid.fg_of_divisive`, `AddSubmonoid.fg_of_subtractive`, `AddSubmonoid.fg_eqLocusM` | `MATHLIB_MODERN_FORM` for the multiplicatively closed application |
| Satz III and explicit multisymmetric bases, lines 9332–9361 | ordinary `MvPolynomial.esymmAlgEquiv` only | `GAP_CANDIDATE` for row symmetry and explicit generators |
| Satz IV, fixed-denominator integral polynomials, lines 9363–9379 | Noetherian polynomial ring and finitely generated ideals are ingredients | small `GAP_CANDIDATE` |
| Factored-form correspondence, lines 9411–9458 | symmetric-polynomial injectivity is partial infrastructure | `GAP_CANDIDATE` after source-specific homogenization |
| Integral and mod-`p` Plücker relation ideal, lines 9534–9594 and 9830–9836 | no pinned coordinate-ring presentation found | high-value `GAP_CANDIDATE` |
| Elementary four-index Plücker identity, lines 9573–9581 | commutative-ring normalization | local `pluckerRelation`; promoted, green bounded build |
| Standard-monomial straightening, lines 9637–9795 | generic normalization infrastructure only | `GAP_CANDIDATE`; source-exact proof also awaits canon review |
| Finite-group averaging, lines 9851–9856 | `GroupAlgebra.average` and representation average-map lemmas | `MATHLIB_EXACT` after action modeling |
| Algebraic-integer finite-group application, lines 9858–9890 | local green `fixedPoints_finiteType` supplies the abstract core | specialization remains a `GAP_CANDIDATE` |

Three formula conflicts at lines 9653, 9699/9703, and 9882/9886 were reported
to the German canon owner. The promoted identity is independent of those
readings and must not be described as Satz I or as generation of the Plücker
ideal. See [integral-invariants-1919.md](integral-invariants-1919.md).

## *Zur Reihenentwicklung in der Formentheorie* (1920)

P16 repairs an earlier proof route and develops determinant-coordinate normal
forms through Fischer projection, polar processes, and Omega operators. Its
three closing notes are authorial mathematical corrections, not transcription
defects.

| Source item | Mathlib coverage | State |
|---|---|---|
| Plücker/minor normal form [1], lines 9921–9931 | determinants, substitution kernels, and quotient congruence are primitives | `GAP_CANDIDATE`; quadratic ideal presentation and distinguished representative missing |
| Dependent-row principal relation ideal [2], lines 9933–9939 | determinant/substitution substrate only | `GAP_CANDIDATE`; `ker(substitution) = (Δ)` missing |
| General substitution congruence [3], lines 9941–9947 | `MvPolynomial.bind₁`; `RingHom.sub_mem_ker_iff` | local `sub_mem_relationIdeal_iff`, `NEW_PACKAGING`; promoted and green |
| Fischer normal form [4]–[6], lines 9949–9985 | polynomial evaluation, derivatives, and eigenspaces are vocabulary only | `GAP_CANDIDATE` |
| Omega series [7]–[9], lines 9986–10034 | no source-shaped operator/commutation package | `GAP_CANDIDATE`; primary print confirms [9]'s leading equality as continuation layout |
| Determinant-coordinate eigenform [10], lines 10036–10055 | determinant and eigenspace infrastructure only | `GAP_CANDIDATE` |
| P08 proof correction, lines 9953–9957 | generic determinant/differential substrate | historical correction recorded; old general identity was only binary |
| P09 conjugate-field correction, line 10061 | `IntermediateField.adjoin`; `normalClosure` | `MATHLIB_MODERN_FORM` substrate |
| P11 finite-number-field correction, line 10063 | `NumberField` exactly supplies finite-dimensionality over `ℚ` | Hilbert irreducibility itself not located by bounded exact-revision search |

The local wrapper states only that two polynomials agree after substitution iff
their difference belongs to the substitution kernel. It does not produce
Noether/Fischer's chosen `Φ`, prove the Plücker presentation, or establish any
series expansion. See [series-expansion-1920.md](series-expansion-1920.md).

## *Moduln in nichtkommutativen Bereichen, insbesondere aus Differential- und Differenzenausdrücken* (1920)

This is a joint work of Emmy Noether and Werner Schmeidler. Its source
“right-sided modules” are Mathlib left submodules: closure is under expressions
`F M`. Source gcd/lcm notation becomes lattice sup/inf, and “Primmodul” means a
maximal submodule with simple quotient rather than a prime ideal.

| Source item | Mathlib coverage | State |
|---|---|---|
| Satz I, quotient decomposition from `M = N ∩ L` and `N + L = ⊤`, line 10329 | quotient kernels, product maps, range, and the first isomorphism theorem exist for noncommutative modules | `NEW_PACKAGING`; forward core promoted with green bounded build |
| Satz II, finite totally coprime decomposition, line 10451 | commutative ideal CRT is exact; generic module infrastructure is partial | `MATHLIB_MODERN_FORM`; source presentation open |
| Satz III and Zusatz, finite bases, lines 10502–10507 | `IsNoetherian` and `Submodule.FG` state the modern consequence | skew triangular operator-ring Noetherianity is a high-value `GAP_CANDIDATE` |
| Satz IV, finite indecomposable decomposition, line 10513 | no direct module Krull–Schmidt/indecomposable API found | `GAP_CANDIDATE` |
| Satz V and Hilfssatz, simple-factor matching, lines 10620–10624 and 10890–10892 | semisimple and `linearEquiv_of_le_sSup` infrastructure supplies the matching core | `MATHLIB_MODERN_FORM`; source dictionary packaging open |
| Satz VI, same-kind iff quotient isomorphism, lines 10630–10644 | quotient lifts and right-multiplication maps are primitives only | high-value `GAP_CANDIDATE` |
| Sätze VIII–X, infinitude of embedded decompositions/prime divisors, lines 10690–10906 | semisimple/isotypic infrastructure is only a scaffold | `GAP_CANDIDATE` |
| Sätze XI–XII, differential systems and analytic solution spaces, lines 10918–10979 | finite-dimensional algebra exists; matching operator/PDE layer does not | `DEFERRED_INFRASTRUCTURE` |

The promoted Satz-I support statement is
`quotientInfEquivProdOfSupEqTop`. Its Lean 4.31 bounded receipt records exit
zero, empty stderr, unchanged source, and a 1,082,052,608-byte process-tree
peak; `#print axioms` reports `propext`, `Classical.choice`, and `Quot.sound`.
It proves only the forward quotient-product core. See
[noncommutative-modules-1920.md](noncommutative-modules-1920.md) for the full
result inventory, joint attribution, source dictionary, and seven reported QA
or scope issues.

## Noether's report on Hentzelt's elimination theory (1921)

P18 is an attribution-sensitive conference report, not a sole-Noether theorem
paper. Nine Hentzelt claims reported by Noether are mapped in
[hentzelt-elimination-report-1921.md](hentzelt-elimination-report-1921.md).

| Source layer | Pinned coverage | State |
|---|---|---|
| common zero set of an ideal, line 11230 | `MvPolynomial.zeroLocus` and membership/antitonicity lemmas | `MATHLIB_EXACT` semantics only |
| generic coordinate change and unique triangular resultant form, lines 11230–11236 | polynomial substitution and matrix substrate | `BLOCKED_SOURCE`; coefficient extension, normalization, and construction are omitted |
| zero-set, divisor-injectivity, and multiplicity claims, lines 11238–11240 | Nullstellensatz sees the radical only | staged triangular semantics are canon/P22-confirmed; exact construction remains a `GAP_CANDIDATE` dependent on P22 definitions |
| linear-forms module, successive ground-module norms, and primary-factor dictionary, line 11240 | monomial bases, Smith/algebra norms, and primary vocabulary are analogies | `BLOCKED_SOURCE`, later `GAP_CANDIDATE`; do not identify Hentzelt's norm with `Algebra.norm` |

## *Idealtheorie in Ringbereichen* (1921)

| Source item | Mathlib declaration | Coverage | Local declaration / state |
|---|---|---|---|
| §1 lines 11346–11368: finite basis / ascending chain, including converse prose | `isNoetherianRing_iff_ideal_fg` | `MATHLIB_MODERN_FORM` | `finiteBasis_iff_noetherian`; green |
| §2, Satz II: finite irreducible decomposition | `exists_infIrred_decomposition` | `MATHLIB_MODERN_FORM` | `finiteIrreducibleDecomposition`; green |
| §4, Definition III: primary ideal | `Ideal.isPrimary_iff` | `MATHLIB_MODERN_FORM` | `primary_iff_factor_or_power`; green |
| §4, Definition IIIa: ideal-product / uniform positive-power formulation | `Ideal.isPrimary_iff` + `Ideal.exists_pow_le_of_le_radical_of_fg` | `NEW_PACKAGING` | `primary_iff_ideal_product_or_power`; green |
| §4, Satz V: unique associated prime and a power relation | `Ideal.isPrime_radical` + `Ideal.exists_radical_pow_le_of_fg` | `NEW_PACKAGING` | `existsUnique_associatedPrime`; green |
| §4, Satz V: gcd / greatest power-contained ideal characterization | `Ideal.IsPrime.le_of_pow_le` and radical infrastructure | `NEW_PACKAGING` | `associatedPrime_isGreatest_powerContained`; green |
| §4, Satz V: least positive exponent | existence lemma + `Nat.find` | `NEW_PACKAGING` | `exists_least_associatedPrimeExponent`; green |
| §4, Satz VI: irreducible implies primary | `InfIrred.isPrimary` | `MATHLIB_EXACT` | `irreducible_isPrimary`; green |
| §5, Satz VIII first direction: finite intersection of primary components with one associated prime | `Ideal.isPrimary_finsetInf` | `MATHLIB_MODERN_FORM` | `primaryFiniteInf_sameAssociatedPrime`; green |
| §5, Zusatz: prime implies irreducible | `Ideal.IsPrime.inf_le` + `InfPrime.infIrred` | `NEW_PACKAGING` | `prime_isIrreducible`; green |
| primary decomposition in Noetherian rings/modules | `Submodule.isLasker` | `MATHLIB_MODERN_FORM` | `primaryDecomposition` |
| first uniqueness theorem | `IsMinimalPrimaryDecomposition.image_radical_eq_associated_primes` | `MATHLIB_MODERN_FORM` | — |
| second uniqueness theorem | `IsMinimalPrimaryDecomposition.comap_localized₀_eq_iInf` | `MATHLIB_MODERN_FORM` | — |

The initial audit had called Satz I and Definition III `MATHLIB_EXACT`. That was
too strong. Satz I itself is the chain-stabilization implication under the
finite-basis condition; the converse follows in surrounding prose. Mathlib's
primary-ideal declaration also makes properness explicit and encodes the
existential power through radical membership. The machine-readable ledger
preserves these limitations instead of flattening them.

Still open in the 1921 work are the converse/reduced-decomposition half of
Satz VIII, source-exact formulations of the two uniqueness theorems, and the
remaining labeled results in §§1–12. A Mathlib anchor is not yet a completed
source audit.

## *Ein algebraisches Kriterium für absolute Irreduzibilität* (1922)

| Source item | Mathlib coverage | State |
|---|---|---|
| Absolute-irreducibility definition, line 12405 | `Irreducible`, algebraic-closure APIs, and `GeometricallyIntegral` are modern ingredients | `MATHLIB_MODERN_FORM`; canonical polynomial predicate still to design |
| Universal reducibility form, lines 12407–12409 and 12581–12585 | no exact construction or criterion found | high-value `GAP_CANDIDATE` |
| Generic universal-coefficient polynomial, lines 12417 and 12439–12444 | only special low-degree irreducibility results found | `GAP_CANDIDATE` |
| Fixed factor-degree condition, lines 12541–12579 | prime-kernel, Noetherian, norm, and symmetric APIs are ingredients only | `GAP_CANDIDATE` |
| Ostrowski specialization, lines 12411–12413 and 12587–12600 | arithmetic/Dedekind/residue-field infrastructure exists; no all-but-finitely-many theorem | high-value `GAP_CANDIDATE` |
| Finite prime-ideal divisors, lines 12594–12598 | `UniqueFactorizationMonoid.fintypeSubtypeDvd` + Dedekind ideal UFM | `NEW_PACKAGING`; green bounded helper build |

See [absolute-irreducibility-1922.md](absolute-irreducibility-1922.md) for the
source caveats and proposed development order. The finite-divisor helper is a
thin arithmetic-tail component and must not be described as the reducibility
form or Ostrowski theorem.

## *Formale Variationsrechnung und Differentialinvarianten* (1922)

This encyclopedia entry is mapped in
[formal-variational-calculus-1922.md](formal-variational-calculus-1922.md),
with Noether's authorship separated from the Riemann–Lipschitz,
Christoffel–Ricci, Levi-Civita, and Weyl material she reports.

| Source layer | Pinned coverage | State |
|---|---|---|
| Euler–Lagrange expressions and central equation, lines 12622–12639 | analysis, differentiation, and integration-by-parts substrate only | `DEFERRED_INFRASTRUCTURE` / `GAP_CANDIDATE`; print resolves the chain to `f(dx)` and `delta f` |
| quadratic specialization and polarization, lines 12639–12665 | finite sums, bilinear forms, polynomial coefficient comparison | `NEW_PACKAGING` / `GAP_CANDIDATE`; capital `D` is print-confirmed as an implicit third formal direction |
| covariant derivative, lines 12667–12671 | `IsCovariantDerivativeOn`; `CovariantDerivative` | `MATHLIB_MODERN_FORM`; coordinate-elimination bridge missing |
| second variation and curvature, lines 12673–12687 | abstract connection/curvature vocabulary | `DEFERRED_INFRASTRUCTURE`; formal variations and substitution-order calculus missing |
| curvature-jet generation and equivalence, line 12689 | no source-shaped reconstruction theorem | `BLOCKED_SOURCE` / `DEFERRED_INFRASTRUCTURE` |
| Noether I and II summary, line 12693 | no pinned variational-symmetry/conservation-law or gauge-identity theorem | major `GAP_CANDIDATE` / `DEFERRED_INFRASTRUCTURE` |

The historical “finite group with rho essential parameters” means a
finite-dimensional Lie group, not a finite-cardinality group.

## *Zur Theorie der Polynomideale und Resultanten* (1923)

P22 is Kurt Hentzelt's mathematics in Emmy Noether's free conceptual
Bearbeitung. Its 31 claim/definition records are mapped in
[hentzelt-polynomial-ideals-resultants-1923.md](hentzelt-polynomial-ideals-resultants-1923.md).

| Source layer | Pinned coverage | State |
|---|---|---|
| ground modules, module quotients, and transition norms, Definitions I--III and Sätze I--V | finite-free modules, Smith normal form, determinant norms, colon ideals | `MATHLIB_MODERN_FORM` substrate; Hentzelt's universal properties and reconstruction theorems remain `GAP_CANDIDATE` |
| generic transforms and ground ideals, Definitions IV--V and Satz VI | polynomial substitution, homogeneous-degree APIs, localization, relative coefficient modules | equation (12), its natural algebraically-independent lower-pair parameters, exact homogeneous degree, arbitrary-input generic leading-coefficient nonvanishing, regular-member existence for every nonzero transformed ideal, characteristic-zero finite specialization to an actual lower-unitriangular equivalence, equation (17), literal late-variable stage submonoids, simultaneous denominator presentation, coefficient reconstruction, and the final transformed-contraction equality are promoted. Successive later-variable regular elements remain `GAP_CANDIDATE`. |
| finite module reduction, Satz VII | finite-free and Smith-normal-form APIs; monic polynomial division; submodule sums and disjointness; `LinearMap.quotientInfEquivSupQuotient`; polynomial function extensionality and finite products | equations (21)--(23) are promoted for a supplied regular divisor: exact bounded representatives, finite coefficient vectors, the bounded-part/principal-tail decomposition, finite free quotient, exact containing-ideal image, and the paired common-tail quotient equivalence with representatives. The last equivalence is explicitly `NEW_PACKAGING` of Mathlib's second isomorphism theorem. Later-stage instantiation, determinant data, the nonunit elementary-divisor theorem, and auxiliary-choice independence remain `GAP_CANDIDATE`. |
| stage resultants and elementary-divisor forms, Definition VI | `associated_norm_prod_smith`, Smith coefficients, determinants | construction/primitive normalization is a central `GAP_CANDIDATE`; not ordinary `Polynomial.resultant` |
| mutual divisibility and vanishing, Satz VIII | ideal radicals and polynomial evaluation | conditional radical and zero-set consequences promoted; divisibilities themselves remain open |
| injectivity and coprime factor splitting, Sätze IX--X | ideal order, CRT, stage norms | substantial staged-elimination gaps |
| principal-ideal residue rank, Satz XI | quotient finrank; univariate PID structure | exact rank `deg h - deg f`, quotient equivalence, and the displayed basis `f, Xf, ...` are promoted |
| successive zeros and multiplicities, Sätze XII--XIII | finite root sets, finite products, Nullstellensatz, splitting, quotient finrank | the coordinatewise root-box containment, explicit finite-product embedding, zero-locus finiteness, and exact `zeroLocus = ∅ ↔ I = ⊤` corollary after Satz XII are promoted; the source's stagewise compatibility, unique extension, and multiplicities remain open |

## *Algebraische und Differentialinvarianten* (1923)

The two halves of P23 are mapped in
[algebraic-differential-invariants-1923.md](algebraic-differential-invariants-1923.md).

| Source layer | Pinned coverage | State |
|---|---|---|
| determinant-weight relative invariants and homogeneous pieces, lines 13554–13577 | `GL`, `SL`, determinants, gradings, and representations are substrate | `NEW_PACKAGING` / `GAP_CANDIDATE`; coefficient-tensor actions and weight-space exhaustion remain |
| Hilbert basis theorem 1, line 13590 | `Polynomial.isNoetherianRing`; `MvPolynomial.isNoetherianRing`; ideal finite generation | `MATHLIB_EXACT` modern content |
| homogeneous-subdomain and invariant-coefficient theorems 2–3, lines 13591–13600 | Noetherian and finite-group averaging ingredients; additive retraction support | theorem 3's coefficient-replacement core is promoted; construction of the GL/Reynolds operator still needs modern reductivity hypotheses |
| integral finite-type theorem 4, line 13603 | integral and finite-type APIs | `BLOCKED_SOURCE` / `GAP_CANDIDATE`; suppressed finiteness hypotheses must be recovered |
| uniform exponent theorem 5, lines 13604–13606 | radical finite generation, radical-power containment, and Nullstellensatz zero-locus semantics | promoted abstract and zero-locus forms, `NEW_PACKAGING`; green bounded build |
| effective degree/exponent bounds, lines 13607–13609 | no coefficient-independent effective package | `DEFERRED_INFRASTRUCTURE`; Hentzelt attribution preserved |
| finite-group resolvent and integral invariants, lines 13613–13615 | orbit products, integrality, and finite-type ingredients | `MATHLIB_MODERN_FORM`; source-shaped generators/specialization open |
| differential reduction, lines 13617–13646 | manifold/connection and algebraic representation vocabulary only | `GAP_CANDIDATE` / `DEFERRED_INFRASTRUCTURE`; finite jet action and variation algebra missing |
| connection-only extension, line 13648 | explicitly posed as open | `BLOCKED_SOURCE`; not an asserted theorem |

## *Eliminationstheorie und allgemeine Idealtheorie* (1923)

All eight Hilfssätze and seventeen Sätze are mapped in
[elimination-ideal-theory-1923.md](elimination-ideal-theory-1923.md).

| Source layer | Mathlib coverage | State |
|---|---|---|
| finite-dimensional prime quotient is a field; proper prime quotient embeds in its fraction field | finite-dimensional domain and fraction-ring APIs | `MATHLIB_EXACT` modern constituents (Hilfssätze III–IV) |
| chain dimension of primes | `Order.coheight`, prime series, `ringKrullDim` | `MATHLIB_MODERN_FORM`; source's prime unit ideal remains a separate convention |
| saturation/localization distributes over finite intersections | `IsLocalization.map_inf`, `IsLocalization.mapFrameHom`, `Ideal.comap_inf` | promoted binary `groundIdeal_inf`, `NEW_PACKAGING`; finite-family/source-stage bridge remains |
| purely inseparable degrees above the separable part are powers of `p` | `separableClosure.isPurelyInseparable`, tower and finrank-power APIs | Hilfssatz VIII is `MATHLIB_MODERN_FORM` |
| successive elementary-divisor forms and Noether's elimination norm | Smith-normal-form, determinant, resultant, and localization substrate only | central `GAP_CANDIDATE`; do not confuse with `Algebra.norm` |
| primary-factor, dimension, absolute-prime, and almost-all-specialization theorems | modern vocabulary exists in pieces | `GAP_CANDIDATE`; depends on elimination norms and missing primary-decomposition/good-reduction infrastructure |

Canon review confirms line 13871's reused `i` as printed dummy-index
overloading and records the line-14039 correction `r_a` to `r_α` in ED0019.
Existing theorem rows remain bound to ED0014 until an explicit rebase.

## *Eliminationstheorie und Idealtheorie* (1924)

All 31 compressed claims and definitions in P25 are mapped in
[elimination-ideal-theory-survey-1924.md](elimination-ideal-theory-survey-1924.md).

| Source layer | Pinned coverage | State |
|---|---|---|
| univariate factorization, root fields, splitting fields, and quotient dimension, lines 14162–14174 | polynomial UFD, `AdjoinRoot`, splitting-field, and finrank APIs | exact or modern coverage; zero-set union is packaging |
| ideals, zero loci, finite bases, prime/primary vocabulary, lines 14176–14180 | `Ideal`; `MvPolynomial.zeroLocus`; Noetherian polynomial rings; radical powers | mostly `MATHLIB_EXACT` / `MATHLIB_MODERN_FORM` |
| irredundant primary decomposition and associated-prime uniqueness, lines 14180–14185 | predicates and radical ingredients only | central `GAP_CANDIDATE` |
| prime quotient, fraction field, and generic zero, line 14187 | quotient-domain, fraction-ring injectivity/surjectivity, `IntermediateField.adjoin`, quotient-kernel, and transcendence-degree/cardinal APIs | relation-ideal equality, field generation, `trdeg≤n`, and `trdeg<n` under `I≠0` are promoted, `NEW_PACKAGING`; the unqualified printed strict form remains apparatus |
| Noether normalization and splitting of a fundamental polynomial, line 14189 | modern normalization and splitting APIs | modern core exists; generic-coordinate/fundamental-polynomial bridge is a gap |
| successive elementary-divisor norm and multiplicity, lines 14189–14199 | Smith, resultant, and module vocabulary are analogies only | `BLOCKED_SOURCE` / `GAP_CANDIDATE`; do not substitute `Algebra.norm` |

## 1924–1925 ideal-theory communications

The three short packets P26–P28 are mapped claim by claim in
[communications-1924-1925.md](communications-1924-1925.md).

| Work | Pinned coverage | State |
|---|---|---|
| P26 abstract ideal-theory characterization, line 14214 | `IsDedekindDomain`, `isDedekindDomain_iff`, and local `artinian_nonzero_quotients_iff_dimensionLEOne` | promoted `isDedekindDomain_iff_integrallyClosed_and_artinianQuotients`, `NEW_PACKAGING`; finite-order promise is `BLOCKED_SOURCE` |
| P27 Hilbert numbers, line 14225 | Hilbert-polynomial, colon-ideal, length, composition-series, and Jordan–Hölder APIs | definitions and index-of-reducibility theorem remain `GAP_CANDIDATE` / `BLOCKED_SOURCE` |
| P28 characters as semisimple group-algebra ideal theory, lines 14236–14238 | Maschke, semisimple modules, isotypic components, and character APIs | mostly `MATHLIB_MODERN_FORM`; explicit block/class bijections are packaging or gaps |

Primary print confirms P27's slash as historical colon-ideal notation and
P28's bare “characters” as source shorthand. Lean uses colon ideals and adds
irreducibility, splitting, and semisimplicity hypotheses explicitly.

## *Der Endlichkeitssatz der Invarianten endlicher linearer Gruppen der Charakteristik p* (1926)

| Source item | Mathlib coverage | State |
|---|---|---|
| Main finite-generation theorem, line 14257 and proof lines 14319–14335 | finite-action integrality is native through `Algebra.IsInvariant.isIntegral`; finite type descends through `fg_of_fg_of_fg` after the module-finite bridge | local `fixedPoints_finiteType`, `FORMALIZED_GAP`; green bounded build |
| Relative- and pointwise-invariant conclusions, lines 14263 and 14337–14339 | the same argument applies to any intermediate subalgebra containing the fixed ring | local `subalgebra_finiteType_of_fixedPoints_le`, `NEW_PACKAGING`; source-specific ring models remain open |
| Finite rational-basis claims, lines 14269–14281 | `IntermediateField.FG` and `Algebra.EssFiniteType` provide partial language and consequences | `GAP_CANDIDATE` |
| Explicit orbit-resolvent generators, lines 14312–14326 | orbit characteristic polynomials and ordinary symmetric-polynomial APIs are ingredients only | `GAP_CANDIDATE` |
| Positive-characteristic root-field criterion, lines 14285–14299 and 14328 | `AdjoinPthRoots` and separable integral-closure finiteness are partial infrastructure | `GAP_CANDIDATE` |

The local main theorem is characteristic-free and more general than the
source's linear action on a polynomial ring: a finite group acts on a
finite-type commutative algebra over a Noetherian base while fixing that base.
The proof does not mistake integrality for finite generation. It first obtains
integrality over the candidate intermediate algebra, derives module-finiteness,
and then uses Artin–Tate to descend finite type. The result is therefore marked
`FORMALIZED_GAP` as a missing combined declaration, not as new historical
mathematics or a claim that its ingredients were absent from Mathlib.

See [modular-invariants-1926.md](modular-invariants-1926.md) for assumptions,
the proof dependency chain, source caveats, and remaining explicit-generator
work.

## *Abstrakter Aufbau der Idealtheorie in algebraischen Zahl- und Funktionenkörpern* (1927)

Noether's axioms at lines 14373–14384 are the ascending chain condition,
descending chains modulo every nonzero ideal, a unit, no zero divisors, and
integral closure in the fraction field. Mathlib's modern characterization
`isDedekindDomain_iff` uses `IsNoetherianRing`, `IsDomain`,
`Ring.DimensionLEOne`, and integral closure. Thus it replaces the paper's
second axiom by dimension at most one.

| Source item | Mathlib coverage | State |
|---|---|---|
| Five-axiom characterization, lines 14354–14389 | `IsDedekindDomain`; `isDedekindDomain_iff` | `MATHLIB_MODERN_FORM`; exact Axiom-II bridge supplied locally |
| Axiom II: DCC modulo every nonzero ideal, lines 14377–14380 | zero-dimensional quotient plus Noetherian implies Artinian in pinned Mathlib | local `artinian_nonzero_quotients_iff_dimensionLEOne`, `FORMALIZED_GAP`; promoted and green |
| Integral elements and transitivity, lines 14589–14678 | `IsIntegral`, `Algebra.IsIntegral.of_finite`, `isIntegral_trans` | exact/modern coverage; source definition packaging optional |
| Dedekind corollaries I and II, lines 14693–14740 | integral-closure and Noetherian infrastructure only | source-shaped `GAP_CANDIDATE`, especially the `m²/n` conclusion |
| Modulsatz, lines 14772–14830 | finite Noetherian/Artinian module transfer | `MATHLIB_MODERN_FORM` |
| Finite separable integral closure, lines 14875–14895 | `IsIntegralClosure.isDedekindDomain` | `MATHLIB_MODERN_FORM` |
| §4 isomorphism theorems and CRT | `Ideal.quotientInfRingEquivPiQuotient`; `Ideal.quotientInfEquivQuotientProd` | `MATHLIB_EXACT` |
| Sätze I–IV, irreducible/primary decomposition and uniqueness, lines 15004–15065 | `exists_infIrred_decomposition`, `InfIrred.isPrimary`, `Submodule.isLasker`, minimal-primary-decomposition APIs | exact/modern coverage; source packaging incomplete |
| Sätze V–VI, primary products and unique prime-power factorization, lines 15081–15233 | `Ideal.uniqueFactorizationMonoid`, `Ideal.dvd_iff_le`, explicit height-one factorization | Satz VI `MATHLIB_MODERN_FORM`; Satz V source package remains a gap |
| Converse development and fractional ideals, lines 15243–15369 | Dedekind and `FractionalIdeal.semifield` infrastructure | fractional-ideal group `MATHLIB_EXACT`; full converse `GAP_CANDIDATE` |
| Double chains iff composition series, lines 15415–15438 | `isFiniteLength_iff_isNoetherian_isArtinian`; `isFiniteLength_iff_exists_compositionSeries` | `MATHLIB_EXACT` |
| Jordan–Hölder, lines 15464–15527 | `CompositionSeries.jordan_holder` with the submodule Jordan–Hölder lattice | `MATHLIB_EXACT` |

The promoted bridge proves, for any commutative Noetherian ring, that every
quotient by a nonzero ideal is Artinian iff the ring has dimension at most one.
The exact proof route uses minimal primes of the quotient and the pinned
Noetherian-zero-dimensional-to-Artinian theorem. Its clean receipt and
`#print axioms` output are recorded in the theorem ledger.

See [dedekind-theory-1927.md](dedekind-theory-1927.md) for the complete result
inventory, exact declaration list, historical 1921-proof correction, and
formalization order.

## *Der Diskriminantensatz für die Ordnungen eines algebraischen Zahl- oder Funktionenkörpers* (1927)

Noether moves from finite algebras over fields to arbitrary finite orders and
then localizes the relative theorem. Her additive “direct sums” are modern
finite ring products, and `Quotientenring` in §8 means localization.

| Source item | Mathlib coverage | State |
|---|---|---|
| §2 primary decomposition and product/CRT decomposition, lines 15706–15763 | `Submodule.isLasker`; minimal primary decomposition; ideal CRT; `IsArtinianRing.equivPi` | `MATHLIB_MODERN_FORM`; source-shaped uniqueness/product package open |
| §3 scalar-extension theorem, lines 15792–15828 | `Algebra.Etale.baseChange`; product classification | forward exact; reverse descent depends on pinned `proof_wanted` and is not axiom-free |
| §3 splitting corollary, lines 15830–15843 | separably-closed splitting API | `GAP_CANDIDATE` for one finite splitting extension |
| §6 discriminant criterion, lines 15992–15994 | field discriminant and trace-pairing criteria | `GAP_CANDIDATE` for arbitrary finite commutative algebras |
| Trace, norm, and embeddings-determinant formulas, lines 15998–16017 | exact field declarations | `MATHLIB_EXACT` |
| Quotient discriminant reduction, line 16041 | `Algebra.trace_quotient_mk`; `Algebra.discr_def`; `RingHom.map_det`; `basisQuotient` | promoted `discr_basisQuotient`, `NEW_PACKAGING`; green bounded build |
| §7 arbitrary-order discriminant theorem, lines 16045–16049 | primary decomposition, quotient, and separability are constituents | major `GAP_CANDIDATE`; canon confirms `u` from the cited setup |
| §8 relative order theorem, lines 16075–16077 | localization, different, and relative norm infrastructure | `GAP_CANDIDATE` |
| Maximal-order ramification criterion, lines 15608 and 16081 | number-field discriminant/different/ramification declarations | `MATHLIB_MODERN_FORM`; derivable but not one source-shaped theorem |

The reverse étale-descent declaration must not be counted as an axiom-free
formalization at this revision: it passes through
`FormallySmooth.of_formallySmooth_tensorProduct_of_faithfullyFlat`, declared
with `proof_wanted`. The promoted quotient-discriminant lemma is independent of
that declaration and does not prove the full order theorem. See
[discriminant-theorem-1927.md](discriminant-theorem-1927.md).

## High-value gap candidates

- The 1916 invariant-system/degree-bound theorem, 1918 variational theorems,
  the 1919 integral Plücker presentation and straightening theorem, the 1920
  Fischer/operator expansion, 1922
  reducibility-form/Ostrowski theorem, the explicit 1926 resolvent and
  root-field criteria, the 1927 Dedekind corollary II and quotient-discriminant
  reduction, arbitrary-order discriminant theorem, later ideal theory, and
  noncommutative algebra remain major development lanes.

An item is promoted from `GAP_CANDIDATE` to `FORMALIZED_GAP` only after both a
source check and a clean build against the declared Mathlib snapshot.
